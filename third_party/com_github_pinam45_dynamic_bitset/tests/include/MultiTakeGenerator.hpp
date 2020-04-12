//
// Copyright (c) 2019 Maxime Pinard
//
// Distributed under the MIT license
// See accompanying file LICENSE or copy at
// https://opensource.org/licenses/MIT
//
#ifndef DYNAMIC_BITSET_MULTITAKEGENERATOR_HPP
#define DYNAMIC_BITSET_MULTITAKEGENERATOR_HPP

#include <catch2/catch.hpp>

#include <algorithm>
#include <tuple>
#include <cassert>

template<typename... T>
constexpr Catch::Generators::GeneratorWrapper<std::tuple<T...>> multitake(
  size_t target,
  Catch::Generators::GeneratorWrapper<T>&&... generators);

template<typename... T>
class MultiTakeGenerator : public Catch::Generators::IGenerator<std::tuple<T...>>
{

public:
	explicit constexpr MultiTakeGenerator(size_t target,
	                                      Catch::Generators::GeneratorWrapper<T>&&... generators);

	constexpr std::tuple<T...> const& get() const override;

	constexpr bool next() override;

private:
	std::tuple<Catch::Generators::GeneratorWrapper<T>...> m_generators;
	std::tuple<T...> m_current;
	size_t m_returned;
	size_t m_target;

	constexpr bool generators_next();

	template<size_t... Is>
	constexpr bool generators_next_impl(std::index_sequence<Is...>);

	constexpr std::tuple<T...> generators_get();

	template<size_t... Is>
	constexpr std::tuple<T...> generators_get_impl(std::index_sequence<Is...>);
};

template<typename... T>
constexpr MultiTakeGenerator<T...>::MultiTakeGenerator(
  size_t target,
  Catch::Generators::GeneratorWrapper<T>&&... generators)
  : m_generators(std::move(generators)...), m_current(), m_returned(0), m_target(target)
{
	assert(target != 0 && "Empty generators are not allowed");
	next();
}

template<typename... T>
constexpr std::tuple<T...> const& MultiTakeGenerator<T...>::get() const
{
	return m_current;
}

template<typename... T>
constexpr bool MultiTakeGenerator<T...>::next()
{
	++m_returned;
	if(m_returned >= m_target)
	{
		return false;
	}

	const bool success = generators_next();
	// If one of the underlying generators does not contain enough values
	// then we cut short as well
	if(!success)
	{
		m_returned = m_target;
	}
	else
	{
		// update current
		m_current = generators_get();
	}
	return success;
}

template<typename... T>
constexpr bool MultiTakeGenerator<T...>::generators_next()
{
	return generators_next_impl(std::make_index_sequence<sizeof...(T)>());
}

template<typename... T>
template<size_t... Is>
constexpr bool MultiTakeGenerator<T...>::generators_next_impl(std::index_sequence<Is...>)
{
	return (std::get<Is>(m_generators).next() && ...);
}

template<typename... T>
constexpr std::tuple<T...> MultiTakeGenerator<T...>::generators_get()
{
	return generators_get_impl(std::make_index_sequence<sizeof...(T)>());
}

template<typename... T>
template<size_t... Is>
constexpr std::tuple<T...> MultiTakeGenerator<T...>::generators_get_impl(std::index_sequence<Is...>)
{
	return std::make_tuple(std::get<Is>(m_generators).get()...);
}

template<typename... T>
constexpr Catch::Generators::GeneratorWrapper<std::tuple<T...>> multitake(
  size_t target,
  Catch::Generators::GeneratorWrapper<T>&&... generators)
{
	return Catch::Generators::GeneratorWrapper<std::tuple<T...>>(
	  std::make_unique<MultiTakeGenerator<T...>>(target, std::move(generators)...));
}

#endif //DYNAMIC_BITSET_MULTITAKEGENERATOR_HPP
