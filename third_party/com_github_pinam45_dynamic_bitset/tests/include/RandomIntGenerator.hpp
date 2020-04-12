//
// Copyright (c) 2019 Maxime Pinard
//
// Distributed under the MIT license
// See accompanying file LICENSE or copy at
// https://opensource.org/licenses/MIT
//
#ifndef DYNAMIC_BITSET_RANDOMINTGENERATOR_HPP
#define DYNAMIC_BITSET_RANDOMINTGENERATOR_HPP

#include <catch2/catch.hpp>

#include <random>

template<typename integral_type>
constexpr Catch::Generators::GeneratorWrapper<integral_type> randomInt(
  std::minstd_rand::result_type seed =
    static_cast<std::minstd_rand::result_type>(std::random_device{}()));

template<typename integral_type>
constexpr Catch::Generators::GeneratorWrapper<integral_type> randomInt(
  integral_type low,
  integral_type high,
  std::minstd_rand::result_type seed =
    static_cast<std::minstd_rand::result_type>(std::random_device{}()));

template<typename integral_type>
class RandomIntGenerator : public Catch::Generators::IGenerator<integral_type>
{
	static_assert(std::is_integral<integral_type>::value,
	              "template argument must be an integral type");

public:
	constexpr explicit RandomIntGenerator(
	  std::minstd_rand::result_type seed =
	    static_cast<std::minstd_rand::result_type>(std::random_device{}()));
	constexpr RandomIntGenerator(
	  integral_type low,
	  integral_type high,
	  std::minstd_rand::result_type seed =
	    static_cast<std::minstd_rand::result_type>(std::random_device{}()));

	constexpr const integral_type& get() const override;
	constexpr bool next() override;

private:
	std::minstd_rand m_rand;
	std::uniform_int_distribution<integral_type> m_dist;
	integral_type m_current_number;
};

template<typename integral_type>
constexpr RandomIntGenerator<integral_type>::RandomIntGenerator(std::minstd_rand::result_type seed)
  : m_rand(seed), m_dist(), m_current_number()
{
	next();
}

template<typename integral_type>
constexpr RandomIntGenerator<integral_type>::RandomIntGenerator(integral_type low,
                                                                integral_type high,
                                                                std::minstd_rand::result_type seed)
  : m_rand(seed), m_dist(low, high), m_current_number()
{
	next();
}

template<typename integral_type>
constexpr const integral_type& RandomIntGenerator<integral_type>::get() const
{
	return m_current_number;
}

template<typename integral_type>
constexpr bool RandomIntGenerator<integral_type>::next()
{
	m_current_number = m_dist(m_rand);
	return true;
}

template<typename integral_type>
constexpr Catch::Generators::GeneratorWrapper<integral_type> randomInt(
  std::minstd_rand::result_type seed)
{
	static_assert(std::is_integral<integral_type>::value,
	              "template argument must be an integral type");
	return Catch::Generators::GeneratorWrapper<integral_type>(
	  std::make_unique<RandomIntGenerator<integral_type>>(seed));
}

template<typename integral_type>
constexpr Catch::Generators::GeneratorWrapper<integral_type> randomInt(
  integral_type low,
  integral_type high,
  std::minstd_rand::result_type seed)
{
	static_assert(std::is_integral<integral_type>::value,
	              "template argument must be an integral type");
	return Catch::Generators::GeneratorWrapper<integral_type>(
	  std::make_unique<RandomIntGenerator<integral_type>>(low, high, seed));
}

#endif //DYNAMIC_BITSET_RANDOMINTGENERATOR_HPP
