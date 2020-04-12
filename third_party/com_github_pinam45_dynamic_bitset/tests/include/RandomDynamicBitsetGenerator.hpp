//
// Copyright (c) 2019 Maxime Pinard
//
// Distributed under the MIT license
// See accompanying file LICENSE or copy at
// https://opensource.org/licenses/MIT
//
#ifndef DYNAMIC_BITSET_RANDOMDYNAMICBITSETGENERATOR_HPP
#define DYNAMIC_BITSET_RANDOMDYNAMICBITSETGENERATOR_HPP

#include <catch2/catch.hpp>
#include <dynamic_bitset.hpp>

#include <random>

template<typename Block>
constexpr Catch::Generators::GeneratorWrapper<dynamic_bitset<Block>> randomDynamicBitset(
  std::minstd_rand::result_type seed =
    static_cast<std::minstd_rand::result_type>(std::random_device{}()));

template<typename Block>
constexpr Catch::Generators::GeneratorWrapper<dynamic_bitset<Block>> randomDynamicBitset(
  typename dynamic_bitset<Block>::size_type min_size,
  typename dynamic_bitset<Block>::size_type max_size,
  std::minstd_rand::result_type seed =
    static_cast<std::minstd_rand::result_type>(std::random_device{}()));

template<typename Block>
class RandomDynamicBitsetGenerator : public Catch::Generators::IGenerator<dynamic_bitset<Block>>
{
public:
	typedef typename dynamic_bitset<Block>::size_type size_type;
	static constexpr size_type default_min_size = 1;
	static constexpr size_type default_max_size = 8 * std::numeric_limits<Block>::digits;

	constexpr explicit RandomDynamicBitsetGenerator(
	  std::minstd_rand::result_type seed =
	    static_cast<std::minstd_rand::result_type>(std::random_device{}()));
	constexpr RandomDynamicBitsetGenerator(
	  size_type min_size,
	  size_type max_size,
	  std::minstd_rand::result_type seed =
	    static_cast<std::minstd_rand::result_type>(std::random_device{}()));

	constexpr const dynamic_bitset<Block>& get() const override;
	constexpr bool next() override;

private:
	std::minstd_rand m_rand;
	std::uniform_int_distribution<size_type> m_size_dist;
	std::uniform_int_distribution<Block> m_block_dist;
	dynamic_bitset<Block> m_current_bitset;
};

template<typename Block>
constexpr RandomDynamicBitsetGenerator<Block>::RandomDynamicBitsetGenerator(
  std::minstd_rand::result_type seed)
  : m_rand(seed)
  , m_size_dist(default_min_size, default_max_size)
  , m_block_dist()
  , m_current_bitset()
{
	next();
}

template<typename Block>
constexpr RandomDynamicBitsetGenerator<Block>::RandomDynamicBitsetGenerator(
  RandomDynamicBitsetGenerator::size_type min_size,
  RandomDynamicBitsetGenerator::size_type max_size,
  std::minstd_rand::result_type seed)
  : m_rand(seed), m_size_dist(min_size, max_size), m_block_dist(), m_current_bitset()
{
	next();
}

template<typename Block>
constexpr const dynamic_bitset<Block>& RandomDynamicBitsetGenerator<Block>::get() const
{
	return m_current_bitset;
}

template<typename Block>
constexpr bool RandomDynamicBitsetGenerator<Block>::next()
{
	const size_type bitset_size = m_size_dist(m_rand);
	m_current_bitset.clear();
	for(size_t i = 0; i < (bitset_size / m_current_bitset.bits_per_block) + 1; ++i)
	{
		m_current_bitset.append(m_block_dist(m_rand));
	}
	m_current_bitset.resize(bitset_size);
	return true;
}

template<typename Block>
constexpr Catch::Generators::GeneratorWrapper<dynamic_bitset<Block>> randomDynamicBitset(
  std::minstd_rand::result_type seed)
{
	return Catch::Generators::GeneratorWrapper<dynamic_bitset<Block>>(
	  std::make_unique<RandomDynamicBitsetGenerator<Block>>(seed));
}

template<typename Block>
constexpr Catch::Generators::GeneratorWrapper<dynamic_bitset<Block>> randomDynamicBitset(
  typename dynamic_bitset<Block>::size_type min_size,
  typename dynamic_bitset<Block>::size_type max_size,
  std::minstd_rand::result_type seed)
{
	return Catch::Generators::GeneratorWrapper<dynamic_bitset<Block>>(
	  std::make_unique<RandomDynamicBitsetGenerator<Block>>(min_size, max_size, seed));
}

#endif //DYNAMIC_BITSET_RANDOMDYNAMICBITSETGENERATOR_HPP
