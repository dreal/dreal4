//
// Copyright (c) 2019 Maxime Pinard
//
// Distributed under the MIT license
// See accompanying file LICENSE or copy at
// https://opensource.org/licenses/MIT
//
#ifndef DYNAMIC_BITSET_RANDOMBITSETSTRINGGENERATOR_HPP
#define DYNAMIC_BITSET_RANDOMBITSETSTRINGGENERATOR_HPP

#include <catch2/catch.hpp>

#include <random>
#include <string>

Catch::Generators::GeneratorWrapper<std::string> randomBitsetString(
  std::minstd_rand::result_type seed =
    static_cast<std::minstd_rand::result_type>(std::random_device{}()));

Catch::Generators::GeneratorWrapper<std::string> randomBitsetString(
  std::string::size_type min_size,
  std::string::size_type max_size,
  std::minstd_rand::result_type seed =
    static_cast<std::minstd_rand::result_type>(std::random_device{}()));

class RandomBitsetStringGenerator : public Catch::Generators::IGenerator<std::string>
{
public:
	typedef std::string::size_type size_type;
	static constexpr size_type default_min_size = 1;
	static constexpr size_type default_max_size = 8 * 32;

	explicit RandomBitsetStringGenerator(
	  std::minstd_rand::result_type seed =
	    static_cast<std::minstd_rand::result_type>(std::random_device{}()));
	RandomBitsetStringGenerator(
	  size_type min_size,
	  size_type max_size,
	  std::minstd_rand::result_type seed =
	    static_cast<std::minstd_rand::result_type>(std::random_device{}()));

	const std::string& get() const override;
	bool next() override;

private:
	std::minstd_rand m_rand;
	std::uniform_int_distribution<size_type> m_size_dist;
	std::bernoulli_distribution m_bit_dist;
	std::string m_current_bitset;
};

RandomBitsetStringGenerator::RandomBitsetStringGenerator(std::minstd_rand::result_type seed)
  : m_rand(seed), m_size_dist(default_min_size, default_max_size), m_bit_dist(), m_current_bitset()
{
	next();
}

RandomBitsetStringGenerator::RandomBitsetStringGenerator(
  RandomBitsetStringGenerator::size_type min_size,
  RandomBitsetStringGenerator::size_type max_size,
  std::minstd_rand::result_type seed)
  : m_rand(seed), m_size_dist(min_size, max_size), m_bit_dist(), m_current_bitset()
{
	next();
}

const std::string& RandomBitsetStringGenerator::get() const
{
	return m_current_bitset;
}

bool RandomBitsetStringGenerator::next()
{
	const size_type bitset_size = m_size_dist(m_rand);
	m_current_bitset.clear();
	m_current_bitset.reserve(bitset_size);
	for(size_t i = 0; i < bitset_size; ++i)
	{
		m_current_bitset.push_back(m_bit_dist(m_rand) ? '1' : '0');
	}
	return true;
}

Catch::Generators::GeneratorWrapper<std::string> randomBitsetString(
  std::minstd_rand::result_type seed)
{
	return Catch::Generators::GeneratorWrapper<std::string>(
	  std::make_unique<RandomBitsetStringGenerator>(seed));
}

Catch::Generators::GeneratorWrapper<std::string> randomBitsetString(
  typename std::string::size_type min_size,
  typename std::string::size_type max_size,
  std::minstd_rand::result_type seed)
{
	return Catch::Generators::GeneratorWrapper<std::string>(
	  std::make_unique<RandomBitsetStringGenerator>(min_size, max_size, seed));
}

#endif //DYNAMIC_BITSET_RANDOMBITSETSTRINGGENERATOR_HPP
