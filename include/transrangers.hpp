/* Transrangers: an efficient, composable design pattern for range processing.
 *
 * Copyright 2021 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://github.com/joaquintides/transrangers for project home page.
 */

#ifndef JOAQUINTIDES_TRANSRANGERS_HPP
#define JOAQUINTIDES_TRANSRANGERS_HPP

#if defined(_MSC_VER)
#pragma once
#endif

#include <iterator>
#include <optional>
#include <tuple>
#include <type_traits>
#include <utility>

#if defined(__clang__)
#define TRANSRANGERS_HOT __attribute__((flatten))
#define TRANSRANGERS_HOT_MUTABLE  __attribute__((flatten)) mutable
#elif defined(__GNUC__)
#define TRANSRANGERS_HOT __attribute__((flatten))
#define TRANSRANGERS_HOT_MUTABLE mutable __attribute__((flatten))
#else
#define TRANSRANGERS_HOT [[msvc::forceinline]]
#define TRANSRANGERS_HOT_MUTABLE mutable [[msvc::forceinline]]
#endif

namespace transrangers{
  
namespace detail
{
  namespace Private
  {
    template <typename, template <typename...> typename>
    struct TIsInstanceImpl : std::false_type {};

    template <template <typename...> typename U, typename...Ts>
    struct TIsInstanceImpl<U<Ts...>, U> : std::true_type {};
  }

  // check if type T is an instantiation of template U
  // @see https://stackoverflow.com/a/61040973
  template <typename T, template <typename ...> typename U>
  using is_instance = Private::TIsInstanceImpl<std::remove_cvref_t<T>, U>;

  template <typename T, template <typename ...> typename U>
  constexpr bool is_instance_v = Private::TIsInstanceImpl<std::remove_cvref_t<T>, U>::value;
}

template<typename Cursor,typename F>
struct ranger_class:F
{
  using cursor=Cursor;
};

template<typename Range>
struct all_copy;

template<class TRanger>
concept is_ranger = (detail::is_instance_v<TRanger, transrangers::ranger_class> || detail::is_instance_v<TRanger, transrangers::all_copy>);

template<typename Cursor,typename F>
auto ranger(F f)
{
  return ranger_class<Cursor,F>{f};
}

namespace detail
{
  template<is_ranger ranger>
  struct ranger_element_type {
    using cursor = ranger::cursor;
    using type = std::decay_t<decltype(*std::declval<cursor>())>;
  };
}

template<typename ranger>
using ranger_element_t = detail::ranger_element_type<ranger>::type;
  
template<typename Range>
auto all(Range&& rng)
{
  using std::begin;
  using std::end;
  using cursor=decltype(begin(rng));

  return ranger<cursor>(
    [first=begin(rng),last=end(rng)](auto dst) TRANSRANGERS_HOT_MUTABLE {
    auto it=first;
    while(it != last) {
        auto current = it;
        ++it;
        if(!dst(current)) {
            first = it;
            return false;
        }
    }
    return true;
  });
}

template<typename Range>
struct all_copy
{
  using ranger=decltype(all(std::declval<Range&>()));
  using cursor= ranger::cursor;

  auto operator()(const auto& p){return rgr(p);}

  Range  rng;
  ranger rgr=all(rng);
};

template<typename Range>
auto all(Range&& rng) requires(std::is_rvalue_reference_v<Range&&>)
{
  return all_copy<Range>{std::move(rng)};
}

template<typename Pred>
auto pred_box(Pred pred)
{
  return [=](auto&&... x)->int{
    return pred(std::forward<decltype(x)>(x)...);
  };
}

template<typename Pred,is_ranger Ranger>
auto filter(Pred pred_,Ranger rgr)
{
  using cursor= Ranger::cursor;

  return ranger<cursor>(
    [=,pred=pred_box(pred_)](auto dst) TRANSRANGERS_HOT_MUTABLE {
    return rgr([&](const auto& p) TRANSRANGERS_HOT {
      return pred(*p)?dst(p):true;
    });
  });
}

template<typename Cursor,typename F,typename=void>
struct deref_fun
{
  decltype(auto) operator*()const{return (*pf)(*p);}

  Cursor p;
  F*     pf;
};

template<typename Cursor,typename F>
struct deref_fun<
  Cursor,F,
  std::enable_if_t<
    std::is_trivially_default_constructible_v<F>&&std::is_empty_v<F>
  >
>
{
  deref_fun(Cursor p={},F* =nullptr):p{p}{}

  decltype(auto) operator*()const{return F()(*p);}

  Cursor p;
};

template<typename F,is_ranger Ranger>
auto transform(F f,Ranger rgr)
{
  using cursor=deref_fun<typename Ranger::cursor,F>;

  return ranger<cursor>([=](auto dst) TRANSRANGERS_HOT_MUTABLE {
    return rgr([&](const auto& p) TRANSRANGERS_HOT {
      return dst(cursor{p,&f});
    });
  });
}

template<is_ranger Ranger>
auto take(int n,Ranger rgr)
{
  using cursor= Ranger::cursor;

  return ranger<cursor>([=](auto dst) TRANSRANGERS_HOT_MUTABLE {
    if(n)return rgr([&](const auto& p) TRANSRANGERS_HOT {
      --n;
      return dst(p)&&(n!=0);
    })||(n==0);
    else return true;
  });
}

template<int count, is_ranger Ranger>
auto take(Ranger rgr)
{
  static_assert(count > 0, "count has to be greater than zero");

  using cursor= Ranger::cursor;

  return transrangers::ranger<cursor>([=](auto dst) TRANSRANGERS_HOT_MUTABLE {
    int n = count;
    return rgr([&](const auto& p) TRANSRANGERS_HOT {
      --n;
      return dst(p)&&(n!=0);
    });
  });
}

template<is_ranger Ranger>
auto concat(Ranger rgr)
{
  return rgr;
}

template<is_ranger Ranger,is_ranger... Rangers>
auto concat(Ranger rgr,Rangers... rgrs)
{
  using cursor= Ranger::cursor;

  return ranger<cursor>(
    [=,cont=false,next=concat(rgrs...)]
    (auto dst) TRANSRANGERS_HOT_MUTABLE {
      if(!cont){
        if(cont=rgr(dst); !cont)return false;
      }
      return next(dst);
    }
  );
}

template<is_ranger Ranger>
auto unique(Ranger rgr)
{
  using cursor= Ranger::cursor;

  return ranger<cursor>(
    [=,start=true,p=cursor{}](auto dst) TRANSRANGERS_HOT_MUTABLE {
    if(start){
      start=false;
      if(rgr([&](const auto& q) TRANSRANGERS_HOT {
        p=q;
        return false;
      }))return true;
      if(!dst(p))return false;
    }
    return rgr([&,prev=p](const auto& q) TRANSRANGERS_HOT_MUTABLE {
      if((*prev==*q)||dst(q)){prev=q;return true;}
      else{p=q;return false;}
    });
  });
}

struct identity_adaption
{
  static decltype(auto) adapt(auto&& srgr){
    return std::forward<decltype(srgr)>(srgr);
  };
};

template<is_ranger Ranger,typename Adaption=identity_adaption>
auto join(Ranger rgr)
{
  using cursor= Ranger::cursor;
  using subranger=std::remove_cvref_t<
    decltype(Adaption::adapt(*std::declval<const cursor&>()))>;
  using subranger_cursor= subranger::cursor;

  return ranger<subranger_cursor>(
    [=,osrgr=std::optional<subranger>{}]
    (auto dst) TRANSRANGERS_HOT_MUTABLE {
    if(osrgr){
      if(!(*osrgr)(dst))return false;
    }
    return rgr([&](const auto& p) TRANSRANGERS_HOT {
      auto srgr=Adaption::adapt(*p);
      if(!srgr(dst)){
        osrgr.emplace(std::move(srgr));
        return false;
      }
      else return true;
    });
  });
}

struct all_adaption
{
  static auto adapt(auto&& srgn){
    return all(std::forward<decltype(srgn)>(srgn));
  };
};

template<is_ranger Ranger>
auto ranger_join(Ranger rgr)
{
  return join<Ranger,all_adaption>(std::move(rgr));
}

template<is_ranger... Rangers>
struct zip_cursor
{
  auto operator*()const
  {
    return std::apply([](const auto&... ps){
      return std::tuple<decltype(*ps)...>{*ps...};
    },ps);
  }

  std::tuple<typename Rangers::cursor...> ps;
};

template<is_ranger Ranger,is_ranger... Rangers>
auto zip(Ranger rgr,Rangers... rgrs)
{
  using cursor=zip_cursor<Ranger,Rangers...>;

  return ranger<cursor>(
    [=,zp=cursor{}](auto dst) TRANSRANGERS_HOT_MUTABLE {
      bool finished=false;
      return rgr([&](const auto& p) TRANSRANGERS_HOT {
        std::get<0>(zp.ps)=p;
        if([&]<std::size_t... I>(std::index_sequence<I...>
#ifdef _MSC_VER
          ,auto&... rgrs1
#endif
        ) TRANSRANGERS_HOT {
          return (rgrs1([&](const auto& p1) TRANSRANGERS_HOT {
            std::get<I+1>(zp.ps)=p1;
            return false;
          })||...);
        }(std::index_sequence_for<Rangers...>{}
#ifdef _MSC_VER
          ,rgrs...
#endif
        )){
          finished=true;
          return false;
        }

        return dst(zp);
      })||finished;
    }
  );
}

template<is_ranger Ranger,typename T>
T accumulate(Ranger rgr,T init)
{
  rgr([&](const auto& p) TRANSRANGERS_HOT{
    init=std::move(init)+*p;
    return true;
  });
  return init;
}

} /* transrangers */

#undef TRANSRANGERS_HOT_MUTABLE
#undef TRANSRANGERS_HOT
#endif
