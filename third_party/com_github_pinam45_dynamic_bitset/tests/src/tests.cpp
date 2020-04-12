//
// Copyright (c) 2019 Maxime Pinard
//
// Distributed under the MIT license
// See accompanying file LICENSE or copy at
// https://opensource.org/licenses/MIT
//
#include "RandomIntGenerator.hpp"
#include "RandomDynamicBitsetGenerator.hpp"
#include "RandomBitsetStringGenerator.hpp"
#include "RandomChunkGenerator.hpp"
#include "MultiTakeGenerator.hpp"

#include <catch2/catch.hpp>
#include <dynamic_bitset.hpp>

#include <algorithm>
#include <vector>
#include <list>
#include <sstream>
#include <cstdint>

constexpr size_t RANDOM_VECTORS_TO_TEST = 100;
constexpr size_t RANDOM_VARIATIONS_TO_TEST = 10;
constexpr std::minstd_rand::result_type SEED = 314159;
//const std::minstd_rand::result_type SEED = std::random_device{}();

template<typename T>
constexpr size_t bits_number = std::numeric_limits<T>::digits;

template<typename T>
constexpr bool bit_value(T value, size_t bit_pos)
{
	static_assert(std::is_unsigned<T>::value, "T is not an unsigned integral type");
	assert(bit_pos < bits_number<T>);
	return (value & (T(1) << bit_pos)) != T(0);
}

TEMPLATE_TEST_CASE("constructors", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);

	SECTION("default constructor")
	{
		dynamic_bitset<TestType> bitset;

		REQUIRE(bitset.empty());
		REQUIRE(bitset.size() == 0);
		REQUIRE(bitset.capacity() == 0);
	}

	SECTION("nbits and init_val constructor")
	{
		CAPTURE(SEED);
		const std::tuple<unsigned long long, size_t> values =
		  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
		                     randomInt<unsigned long long>(SEED),
		                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1)));
		const unsigned long long value = std::get<0>(values);
		const size_t bits_to_take = std::get<1>(values);
		CAPTURE(value, bits_to_take);

		dynamic_bitset<TestType> bitset(bits_to_take, value);
		CAPTURE(bitset);

		// check init value bits
		for(size_t i = 0; i < bits_to_take; ++i)
		{
			CAPTURE(i);
			REQUIRE(bitset[i] == bit_value(value, i));
		}
	}

	SECTION("initializer_list constructor")
	{
		SECTION("one value")
		{
			const TestType init_value =
			  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomInt<TestType>(SEED)));
			const dynamic_bitset<TestType> bitset = {init_value};
			CAPTURE(init_value, bitset);

			// check bits
			for(size_t i = 0; i < bits_number<TestType>; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bit_value(init_value, i));
			}
		}

		SECTION("two values")
		{
			const std::tuple<TestType, TestType> init_values = GENERATE(multitake(
			  RANDOM_VECTORS_TO_TEST, randomInt<TestType>(SEED), randomInt<TestType>(SEED + 1)));
			std::initializer_list<TestType> init_values_list = {std::get<0>(init_values),
			                                                    std::get<1>(init_values)};
			const dynamic_bitset<TestType> bitset = init_values_list;
			CAPTURE(bitset, init_values_list);

			// check bits
			size_t value_i = 0;
			for(const TestType& value: init_values_list)
			{
				for(size_t bit_i = 0; bit_i < bits_number<TestType>; ++bit_i)
				{
					CAPTURE(value_i, bit_i);
					REQUIRE(bitset[value_i * bits_number<TestType> + bit_i]
					        == bit_value(value, bit_i));
				}
				++value_i;
			}
		}
	}

	SECTION("string constructor")
	{
		const std::tuple<unsigned long long, size_t> values =
		  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
		                     randomInt<unsigned long long>(SEED),
		                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1)));
		const unsigned long long value = std::get<0>(values);
		const size_t bits_to_take = std::get<1>(values);
		CAPTURE(value, bits_to_take);

		std::string str(bits_to_take, '0');
		const size_t size = str.size();
		for(size_t i = 0; i < bits_to_take; ++i)
		{
			if(bit_value(value, i))
			{
				str[size - 1 - i] = '1';
			}
		}
		CAPTURE(str);

		SECTION("full string")
		{
			SECTION("std::string_view")
			{
				const dynamic_bitset<TestType> bitset(std::string_view{str});
				CAPTURE(bitset);

				for(size_t i = 0; i < bits_to_take; ++i)
				{
					CAPTURE(i);
					REQUIRE(bitset[i] == bit_value(value, i));
				}

				REQUIRE(bitset.to_string() == str);
			}

			SECTION("std::string")
			{
				const dynamic_bitset<TestType> bitset(str);
				CAPTURE(bitset);

				for(size_t i = 0; i < bits_to_take; ++i)
				{
					CAPTURE(i);
					REQUIRE(bitset[i] == bit_value(value, i));
				}

				REQUIRE(bitset.to_string() == str);
			}

			SECTION("const char*")
			{
				const dynamic_bitset<TestType> bitset(str.c_str());
				CAPTURE(bitset);

				for(size_t i = 0; i < bits_to_take; ++i)
				{
					CAPTURE(i);
					REQUIRE(bitset[i] == bit_value(value, i));
				}

				REQUIRE(bitset.to_string() == str);
			}
		}

		SECTION("partial string")
		{
			const std::tuple<size_t, size_t> parameters = GENERATE(multitake(
			  RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 2), randomInt<size_t>(SEED + 3)));
			const size_t pos = std::get<0>(parameters) % bits_to_take;
			const size_t n =
			  (pos == (bits_to_take - 1)) ? std::get<1>(parameters) % (bits_to_take - pos) : 0;
			CAPTURE(pos, n);

			SECTION("std::string_view")
			{
				const dynamic_bitset<TestType> bitset(std::string_view{str}, pos, n);
				CAPTURE(bitset);

				for(size_t i = 0; i < n; ++i)
				{
					CAPTURE(i);
					REQUIRE(bitset[i] == bit_value(value, pos + i));
				}
			}

			SECTION("std::string")
			{
				const dynamic_bitset<TestType> bitset(str, pos, n);
				CAPTURE(bitset);

				for(size_t i = 0; i < n; ++i)
				{
					CAPTURE(i);
					REQUIRE(bitset[i] == bit_value(value, pos + i));
				}
			}

			SECTION("const char*")
			{
				const dynamic_bitset<TestType> bitset(str.c_str(), pos, n);
				CAPTURE(bitset);

				for(size_t i = 0; i < n; ++i)
				{
					CAPTURE(i);
					REQUIRE(bitset[i] == bit_value(value, pos + i));
				}
			}
		}
	}
}

TEMPLATE_TEST_CASE("resize", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	dynamic_bitset<TestType> bitset =
	  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
	CAPTURE(bitset);

	SECTION("resizing to 0")
	{
		bitset.resize(0);
		REQUIRE(bitset.empty());
		REQUIRE(bitset.size() == 0);
	}

	SECTION("resizing to the same size")
	{
		const size_t size_save = bitset.size();
		bitset.resize(bitset.size());
		REQUIRE(bitset.size() == size_save);
	}

	SECTION("changing size")
	{
		size_t size_change =
		  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(0, 128, SEED + 1)));
		const bool new_values = GENERATE(true, false);
		CAPTURE(size_change, new_values);

		SECTION("incrementing size")
		{
			const dynamic_bitset<TestType> bitset_copy = bitset;
			const size_t new_size = bitset.size() + size_change;
			bitset.resize(new_size, new_values);
			REQUIRE(bitset.size() == new_size);

			for(size_t i = 0; i < bitset_copy.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
			for(size_t i = bitset_copy.size(); i < bitset.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == new_values);
			}
		}

		SECTION("decrementing size")
		{
			const dynamic_bitset<TestType> bitset_copy = bitset;
			const size_t new_size = size_change > bitset.size() ? 0 : size_change;
			bitset.resize(new_size, new_values);
			REQUIRE(bitset.size() == new_size);

			for(size_t i = 0; i < bitset.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
		}
	}
}

TEMPLATE_TEST_CASE("clear", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	dynamic_bitset<TestType> bitset =
	  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
	CAPTURE(bitset);

	bitset.clear();
	REQUIRE(bitset.empty());
	REQUIRE(bitset.size() == 0);
}

TEMPLATE_TEST_CASE("push_back", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	std::tuple<dynamic_bitset<TestType>, dynamic_bitset<TestType>> values =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomDynamicBitset<TestType>(SEED),
	                     randomDynamicBitset<TestType>(1, 2 * bits_number<TestType>, SEED + 1)));
	dynamic_bitset<TestType>& bitset = std::get<0>(values);
	dynamic_bitset<TestType>& to_push = std::get<1>(values);
	CAPTURE(bitset, to_push);

	const dynamic_bitset<TestType> bitset_copy = bitset;
	size_t size = bitset.size();

	// new bits added
	for(size_t i = 0; i < to_push.size(); ++i)
	{
		CAPTURE(i, size);
		bitset.push_back(to_push[i]);
		REQUIRE(bitset[size] == to_push[i]);
		++size;
		REQUIRE(bitset.size() == size);
	}

	// initial bits not changed
	for(size_t i = 0; i < bitset_copy.size(); ++i)
	{
		CAPTURE(i);
		REQUIRE(bitset[i] == bitset_copy[i]);
	}
}

TEMPLATE_TEST_CASE("pop_back", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);

	SECTION("empty bitset")
	{
		dynamic_bitset<TestType> bitset;

		bitset.pop_back();
		REQUIRE(bitset.empty());
	}

	SECTION("non-empty bitset")
	{
		std::tuple<dynamic_bitset<TestType>, size_t> values =
		  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
		                     randomDynamicBitset<TestType>(SEED),
		                     randomInt<TestType>(1, 2 * bits_number<TestType>, SEED + 1)));
		dynamic_bitset<TestType>& bitset = std::get<0>(values);
		size_t to_pop = std::min(bitset.size(), std::get<1>(values));
		CAPTURE(bitset, to_pop);

		const dynamic_bitset<TestType> bitset_copy = bitset;
		size_t size = bitset.size();

		// bits removed
		for(size_t i = 0; i < to_pop; ++i)
		{
			CAPTURE(i, size);
			bitset.pop_back();
			--size;
			REQUIRE(bitset.size() == size);
		}

		// initial bits not changed
		for(size_t i = 0; i < bitset.size(); ++i)
		{
			CAPTURE(i);
			REQUIRE(bitset[i] == bitset_copy[i]);
		}
	}
}

TEMPLATE_TEST_CASE("append", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	dynamic_bitset<TestType> bitset =
	  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
	CAPTURE(bitset);
	const dynamic_bitset<TestType> bitset_copy = bitset;

	SECTION("one value")
	{
		const TestType value =
		  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<TestType>(SEED + 1)));
		CAPTURE(value);

		bitset.append(value);
		REQUIRE(bitset.size() == (bitset_copy.size() + bits_number<TestType>));

		// new bits added
		for(size_t i = 0; i < bits_number<TestType>; ++i)
		{
			CAPTURE(i);
			REQUIRE(bitset[bitset_copy.size() + i] == bit_value(value, i));
		}

		// initial bits not changed
		for(size_t i = 0; i < bitset_copy.size(); ++i)
		{
			CAPTURE(i);
			REQUIRE(bitset[i] == bitset_copy[i]);
		}
	}

	SECTION("empty initializer_list")
	{
		bitset.append({});
		REQUIRE(bitset.size() == bitset_copy.size());
	}

	SECTION("two values initializer_list")
	{
		const std::tuple<TestType, TestType> init_values = GENERATE(multitake(
		  RANDOM_VARIATIONS_TO_TEST, randomInt<TestType>(SEED + 1), randomInt<TestType>(SEED + 2)));
		std::initializer_list<TestType> values = {std::get<0>(init_values),
		                                          std::get<1>(init_values)};
		CAPTURE(values);

		bitset.append(values);
		REQUIRE(bitset.size() == (bitset_copy.size() + values.size() * bits_number<TestType>));

		// new bits added
		size_t value_i = 0;
		for(const TestType& value: values)
		{
			for(size_t bit_i = 0; bit_i < bits_number<TestType>; ++bit_i)
			{
				CAPTURE(value_i, bit_i);
				REQUIRE(bitset[bitset_copy.size() + value_i * bits_number<TestType> + bit_i]
				        == bit_value(value, bit_i));
			}
			++value_i;
		}

		// initial bits not changed
		for(size_t i = 0; i < bitset_copy.size(); ++i)
		{
			CAPTURE(i);
			REQUIRE(bitset[i] == bitset_copy[i]);
		}
	}

	SECTION("same iterators")
	{
		const std::vector<TestType> values;

		bitset.append(std::cbegin(values), std::cend(values));
		REQUIRE(bitset.size() == bitset_copy.size());
	}

	SECTION("random access iterators")
	{
		const std::vector<TestType> values =
		  GENERATE(take(RANDOM_VARIATIONS_TO_TEST,
		                randomChunk<TestType>(2, 5, randomInt<TestType>(SEED + 1), SEED + 2)));
		CAPTURE(values);

		bitset.append(std::cbegin(values), std::cend(values));
		REQUIRE(bitset.size() == (bitset_copy.size() + values.size() * bits_number<TestType>));

		// new bits added
		size_t value_i = 0;
		for(const TestType& value: values)
		{
			for(size_t bit_i = 0; bit_i < bits_number<TestType>; ++bit_i)
			{
				CAPTURE(value_i, bit_i);
				REQUIRE(bitset[bitset_copy.size() + value_i * bits_number<TestType> + bit_i]
				        == bit_value(value, bit_i));
			}
			++value_i;
		}

		// initial bits not changed
		for(size_t i = 0; i < bitset_copy.size(); ++i)
		{
			CAPTURE(i);
			REQUIRE(bitset[i] == bitset_copy[i]);
		}
	}

	SECTION("bidirectional iterators")
	{
		const std::vector<TestType> values =
		  GENERATE(take(RANDOM_VARIATIONS_TO_TEST,
		                randomChunk<TestType>(2, 5, randomInt<TestType>(SEED + 1), SEED + 2)));
		CAPTURE(values);

		const std::list<TestType> values_list(std::cbegin(values), std::cend(values));
		bitset.append(std::cbegin(values_list), std::cend(values_list));
		REQUIRE(bitset.size() == (bitset_copy.size() + values.size() * bits_number<TestType>));

		// new bits added
		size_t value_i = 0;
		for(const TestType& value: values)
		{
			for(size_t bit_i = 0; bit_i < bits_number<TestType>; ++bit_i)
			{
				CAPTURE(value_i, bit_i);
				REQUIRE(bitset[bitset_copy.size() + value_i * bits_number<TestType> + bit_i]
				        == bit_value(value, bit_i));
			}
			++value_i;
		}

		// initial bits not changed
		for(size_t i = 0; i < bitset_copy.size(); ++i)
		{
			CAPTURE(i);
			REQUIRE(bitset[i] == bitset_copy[i]);
		}
	}
}

TEMPLATE_TEST_CASE("bitwise operators", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	const std::tuple<unsigned long long, unsigned long long, size_t> values =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomInt<unsigned long long>(SEED),
	                     randomInt<unsigned long long>(SEED + 1),
	                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 2)));
	unsigned long long value1 = std::get<0>(values);
	const unsigned long long value2 = std::get<1>(values);
	const size_t bits_to_take = std::get<2>(values);
	CAPTURE(value1, value2, bits_to_take);

	dynamic_bitset<TestType> bitset1(bits_to_take, value1);
	const dynamic_bitset<TestType> bitset2(bits_to_take, value2);
	CAPTURE(bitset1, bitset2);

	SECTION("assignement operators")
	{
		SECTION("operator&=")
		{
			bitset1 &= bitset2;
			value1 &= value2;

			// check bits
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset1[i] == bit_value(value1, i));
			}
		}

		SECTION("operator|=")
		{
			bitset1 |= bitset2;
			value1 |= value2;

			// check bits
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset1[i] == bit_value(value1, i));
			}
		}

		SECTION("operator^=")
		{
			bitset1 ^= bitset2;
			value1 ^= value2;

			// check bits
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset1[i] == bit_value(value1, i));
			}
		}

		SECTION("operator-=")
		{
			bitset1 -= bitset2;
			value1 &= ~value2;

			// check bits
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset1[i] == bit_value(value1, i));
			}
		}
	}

	SECTION("binary operators")
	{
		SECTION("operator&")
		{
			const dynamic_bitset<TestType> bitset = bitset1 & bitset2;
			const unsigned long long value = value1 & value2;

			// check bits
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bit_value(value, i));
			}
		}

		SECTION("operator|")
		{
			const dynamic_bitset<TestType> bitset = bitset1 | bitset2;
			const unsigned long long value = value1 | value2;

			// check bits
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bit_value(value, i));
			}
		}

		SECTION("operator^")
		{
			const dynamic_bitset<TestType> bitset = bitset1 ^ bitset2;
			const unsigned long long value = value1 ^ value2;

			// check bits
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bit_value(value, i));
			}
		}

		SECTION("operator-")
		{
			const dynamic_bitset<TestType> bitset = bitset1 - bitset2;
			const unsigned long long value = value1 & ~value2;

			// check bits
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bit_value(value, i));
			}
		}
	}
}

TEMPLATE_TEST_CASE("shift operators", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);

	SECTION("null shifts")
	{
		dynamic_bitset<TestType> bitset =
		  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
		CAPTURE(bitset);

		dynamic_bitset<TestType> bitset_copy = bitset;

		SECTION("assignement operators")
		{
			bitset <<= 0;
			REQUIRE(bitset == bitset_copy);
			bitset >>= 0;
			REQUIRE(bitset == bitset_copy);
		}

		SECTION("binary operators")
		{
			dynamic_bitset<TestType> result = bitset << 0;
			REQUIRE(bitset == bitset_copy);
			result = bitset >> 0;
			REQUIRE(bitset == bitset_copy);
		}
	}

	SECTION("real shifts")
	{
		const std::tuple<unsigned long long, size_t, size_t> values =
		  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
		                     randomInt<unsigned long long>(SEED),
		                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1),
		                     randomInt<size_t>(0, bits_number<unsigned long long> - 1, SEED + 2)));
		unsigned long long value = std::get<0>(values);
		const size_t bits_to_take = std::get<1>(values);
		const size_t shift = std::get<2>(values);
		CAPTURE(value, bits_to_take, shift);

		dynamic_bitset<TestType> bitset(bits_to_take, value);
		CAPTURE(bitset);

		SECTION("assignement operators")
		{
			SECTION("operator<<=")
			{
				bitset <<= shift;
				value <<= shift;

				// check bits
				for(size_t i = 0; i < bits_to_take; ++i)
				{
					CAPTURE(i);
					REQUIRE(bitset[i] == bit_value(value, i));
				}
			}

			SECTION("operator>>=")
			{
				bitset >>= shift;
				value &= ~static_cast<unsigned long long>(0)
				         >> (bits_number<
				               unsigned long long> - bits_to_take); // set not taken left bits to 0
				value >>= shift;

				// check bits
				for(size_t i = 0; i < bits_to_take; ++i)
				{
					CAPTURE(i);
					REQUIRE(bitset[i] == bit_value(value, i));
				}
			}
		}

		SECTION("binary operators")
		{
			SECTION("operator<<")
			{
				const dynamic_bitset<TestType> shifted_bitset = bitset << shift;
				const unsigned long long shifted_value = value << shift;

				// check bits
				for(size_t i = 0; i < bits_to_take; ++i)
				{
					CAPTURE(i);
					REQUIRE(shifted_bitset[i] == bit_value(shifted_value, i));
				}
			}

			SECTION("operator>>")
			{
				const dynamic_bitset<TestType> shifted_bitset = bitset >> shift;
				const unsigned long long shifted_value =
				  (value
				   & (~static_cast<unsigned long long>(0)
				      >> (bits_number<unsigned long long> - bits_to_take)))
				  >> shift;

				// check bits
				for(size_t i = 0; i < bits_to_take; ++i)
				{
					CAPTURE(i);
					REQUIRE(shifted_bitset[i] == bit_value(shifted_value, i));
				}
			}
		}
	}
}

TEMPLATE_TEST_CASE("operator~", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	const std::tuple<unsigned long long, size_t> values =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomInt<unsigned long long>(SEED),
	                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1)));
	unsigned long long value = std::get<0>(values);
	const size_t bits_to_take = std::get<1>(values);
	CAPTURE(value, bits_to_take);

	dynamic_bitset<TestType> bitset(bits_to_take, value);
	CAPTURE(bitset);

	// operator~
	bitset = ~bitset;
	value = ~value;

	// check bits
	for(size_t i = 0; i < bits_to_take; ++i)
	{
		CAPTURE(i);
		REQUIRE(bitset[i] == bit_value(value, i));
	}
}

TEMPLATE_TEST_CASE("set reset flip", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	dynamic_bitset<TestType> bitset = GENERATE(take(
	  RANDOM_VECTORS_TO_TEST,
	  randomDynamicBitset<TestType>(3 * bits_number<TestType>, 8 * bits_number<TestType>, SEED)));
	CAPTURE(bitset);

	SECTION("range")
	{
		const std::tuple<size_t, size_t> values = GENERATE(multitake(
		  RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 1), randomInt<size_t>(SEED + 2)));
		const size_t pos = std::get<0>(values) % bitset.size();
		const size_t len = std::get<1>(values) % (bitset.size() - pos);
		CAPTURE(pos, len);

		const dynamic_bitset<TestType> bitset_copy = bitset;

		SECTION("set")
		{
			const bool set_to = GENERATE(true, false);
			CAPTURE(set_to);

			bitset.set(0, 0, set_to);
			REQUIRE(bitset == bitset_copy);

			bitset.set(pos, 0, set_to);
			REQUIRE(bitset == bitset_copy);

			bitset.set(pos, len, set_to);

			// check bits
			for(size_t i = 0; i < pos; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
			for(size_t i = 0; i < len; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[pos + i] == set_to);
			}
			for(size_t i = pos + len; i < bitset.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
		}

		SECTION("reset")
		{
			bitset.reset(0, 0);
			REQUIRE(bitset == bitset_copy);

			bitset.reset(pos, 0);
			REQUIRE(bitset == bitset_copy);

			bitset.reset(pos, len);

			// check bits
			for(size_t i = 0; i < pos; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
			for(size_t i = 0; i < len; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[pos + i] == false);
			}
			for(size_t i = pos + len; i < bitset.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
		}

		SECTION("flip")
		{
			bitset.flip(0, 0);
			REQUIRE(bitset == bitset_copy);

			bitset.flip(pos, 0);
			REQUIRE(bitset == bitset_copy);

			bitset.flip(pos, len);

			// check bits
			for(size_t i = 0; i < pos; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
			for(size_t i = 0; i < len; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[pos + i] != bitset_copy[pos + i]);
			}
			for(size_t i = pos + len; i < bitset.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
		}
	}

	SECTION("single bit")
	{
		const size_t pos =
		  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 1))) % bitset.size();
		CAPTURE(pos);

		const dynamic_bitset<TestType> bitset_copy = bitset;

		SECTION("set")
		{
			const bool set_to = GENERATE(true, false);
			CAPTURE(set_to);
			bitset.set(pos, set_to);

			// check bits
			for(size_t i = 0; i < pos; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
			REQUIRE(bitset[pos] == set_to);
			for(size_t i = pos + 1; i < bitset.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
		}

		SECTION("reset")
		{
			bitset.reset(pos);

			// check bits
			for(size_t i = 0; i < pos; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
			REQUIRE(bitset[pos] == false);
			for(size_t i = pos + 1; i < bitset.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
		}

		SECTION("flip")
		{
			bitset.flip(pos);

			// check bits
			for(size_t i = 0; i < pos; ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
			REQUIRE(bitset[pos] != bitset_copy[pos]);
			for(size_t i = pos + 1; i < bitset.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] == bitset_copy[i]);
			}
		}
	}

	SECTION("all bits")
	{
		SECTION("set")
		{
			bitset.set();

			// check bits
			REQUIRE(bitset.all());
		}

		SECTION("reset")
		{
			bitset.reset();

			// check bits
			REQUIRE(bitset.none());
		}

		SECTION("flip")
		{
			const dynamic_bitset<TestType> bitset_copy = bitset;
			bitset.flip();

			// check bits
			for(size_t i = 0; i < bitset.size(); ++i)
			{
				CAPTURE(i);
				REQUIRE(bitset[i] != bitset_copy[i]);
			}
		}
	}
}

TEMPLATE_TEST_CASE("test", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	const std::tuple<unsigned long long, size_t> values =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomInt<unsigned long long>(SEED),
	                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1)));
	unsigned long long value = std::get<0>(values);
	const size_t bits_to_take = std::get<1>(values);
	CAPTURE(value, bits_to_take);

	dynamic_bitset<TestType> bitset(bits_to_take, value);
	CAPTURE(bitset);

	// check
	for(size_t i = 0; i < bits_to_take; ++i)
	{
		CAPTURE(i);
		REQUIRE(bitset.test(i) == bit_value(value, i));
	}
}

TEMPLATE_TEST_CASE("test_set", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	const std::tuple<unsigned long long, size_t> values =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomInt<unsigned long long>(SEED),
	                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1)));
	unsigned long long value = std::get<0>(values);
	const size_t bits_to_take = std::get<1>(values);
	const bool set_to = GENERATE(true, false);
	CAPTURE(value, bits_to_take, set_to);

	dynamic_bitset<TestType> bitset(bits_to_take, value);
	CAPTURE(bitset);

	// check
	for(size_t i = 0; i < bits_to_take; ++i)
	{
		CAPTURE(i);
		REQUIRE(bitset.test_set(i, set_to) == bit_value(value, i));
		REQUIRE(bitset[i] == set_to);
	}
}

TEMPLATE_TEST_CASE("all any none", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	SECTION("empty bitset")
	{
		dynamic_bitset<TestType> bitset;
		CAPTURE(bitset);

		REQUIRE(bitset.all());
		REQUIRE_FALSE(bitset.any());
		REQUIRE(bitset.none());
	}

	SECTION("non-empty bitset")
	{
		CAPTURE(SEED);
		const size_t bitset_size = GENERATE(
		  take(RANDOM_VECTORS_TO_TEST,
		       randomInt<size_t>(3 * bits_number<TestType>, 8 * bits_number<TestType>, SEED)));
		CAPTURE(bitset_size);

		dynamic_bitset<TestType> bitset(bitset_size);
		CAPTURE(bitset);

		SECTION("all bits on")
		{
			bitset.set();
			REQUIRE(bitset.all());
			REQUIRE(bitset.any());
			REQUIRE_FALSE(bitset.none());
		}

		SECTION("one bit on")
		{
			const size_t pos =
			  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 1))) % bitset_size;
			CAPTURE(pos);
			bitset.reset();
			bitset.set(pos);
			REQUIRE_FALSE(bitset.all());
			REQUIRE(bitset.any());
			REQUIRE_FALSE(bitset.none());
		}

		SECTION("no bit on")
		{
			bitset.reset();
			REQUIRE_FALSE(bitset.all());
			REQUIRE_FALSE(bitset.any());
			REQUIRE(bitset.none());
		}
	}
}

TEMPLATE_TEST_CASE("count", "[dynamic_bitset][libpopcnt][builtin]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);

	SECTION("empty bitset")
	{
		dynamic_bitset<TestType> bitset;

		REQUIRE(bitset.count() == 0);
	}

	SECTION("non-empty bitset")
	{
		dynamic_bitset<TestType> bitset =
		  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
		CAPTURE(bitset);

		size_t count = 0;
		for(size_t i = 0; i < bitset.size(); ++i)
		{
			count += static_cast<size_t>(bitset[i]);
		}

		REQUIRE(bitset.count() == count);
	}
}

TEMPLATE_TEST_CASE("array subscript operator", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	const std::tuple<unsigned long long, size_t> values =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomInt<unsigned long long>(SEED),
	                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1)));
	unsigned long long value = std::get<0>(values);
	const size_t bits_to_take = std::get<1>(values);
	CAPTURE(value, bits_to_take);

	dynamic_bitset<TestType> bitset(bits_to_take, value);
	CAPTURE(bitset);

	SECTION("access")
	{
		for(size_t i = 0; i < bits_to_take; ++i)
		{
			CAPTURE(i);
			REQUIRE(bitset[i] == bit_value(value, i));
		}
	}

	SECTION("reference operator=")
	{
		const unsigned long long other_value =
		  GENERATE(take(1, randomInt<unsigned long long>(SEED + 2)));
		dynamic_bitset<TestType> other_bitset(bits_to_take, other_value);
		CAPTURE(other_bitset);

		SECTION("with bool")
		{
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				bitset[i] = other_bitset.test(i);
			}
			REQUIRE(bitset == other_bitset);
		}

		SECTION("with reference")
		{
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				bitset[i] = other_bitset[i];
			}
			REQUIRE(bitset == other_bitset);
		}
	}

	SECTION("reference binary operators")
	{
		const unsigned long long other_value =
		  GENERATE(take(1, randomInt<unsigned long long>(SEED + 2)));
		dynamic_bitset<TestType> other_bitset(bits_to_take, other_value);
		CAPTURE(other_bitset);

		dynamic_bitset<TestType> bitset_copy = bitset;

		SECTION("operator&=")
		{
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				bitset[i] &= other_bitset[i];
			}

			bitset_copy &= other_bitset;
			REQUIRE(bitset == bitset_copy);
		}

		SECTION("operator|=")
		{
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				bitset[i] |= other_bitset[i];
			}

			bitset_copy |= other_bitset;
			REQUIRE(bitset == bitset_copy);
		}

		SECTION("operator^=")
		{
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				bitset[i] ^= other_bitset[i];
			}

			bitset_copy ^= other_bitset;
			REQUIRE(bitset == bitset_copy);
		}

		SECTION("operator-=")
		{
			for(size_t i = 0; i < bits_to_take; ++i)
			{
				bitset[i] -= other_bitset[i];
			}

			bitset_copy -= other_bitset;
			REQUIRE(bitset == bitset_copy);
		}
	}

	SECTION("reference operator~")
	{
		for(size_t i = 0; i < bits_to_take; ++i)
		{
			CAPTURE(i);
			REQUIRE(~bitset[i] == !bit_value(value, i));
		}
	}

	SECTION("set reset flip assign")
	{
		const size_t pos =
		  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 2))) % bits_to_take;
		CAPTURE(pos);

		SECTION("set")
		{
			bitset[pos].set();
			REQUIRE(bitset[pos] == true);
		}

		SECTION("reset")
		{
			bitset[pos].reset();
			REQUIRE(bitset[pos] == false);
		}

		SECTION("flip")
		{
			bitset[pos].flip();
			REQUIRE(bitset[pos] == !bit_value(value, pos));
		}

		SECTION("assign")
		{
			const bool new_value = GENERATE(true, false);
			CAPTURE(new_value);
			bitset[pos].assign(new_value);
			REQUIRE(bitset[pos] == new_value);
		}
	}
}

TEMPLATE_TEST_CASE("size num_blocks empty capacity",
                   "[dynamic_bitset]",
                   uint16_t,
                   uint32_t,
                   uint64_t)
{
	CAPTURE(SEED);
	const std::tuple<unsigned long long, size_t> values =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomInt<unsigned long long>(SEED),
	                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1)));
	unsigned long long value = std::get<0>(values);
	const size_t bits_to_take = std::get<1>(values);
	CAPTURE(value, bits_to_take);

	dynamic_bitset<TestType> bitset(bits_to_take, value);
	CAPTURE(bitset);

	// size
	REQUIRE(bitset.size() == bits_to_take);

	// num_blocks
	const size_t num_blocks =
	  bits_to_take
	    / bits_number<TestType> + static_cast<size_t>(bits_to_take % bits_number<TestType>> 0);
	REQUIRE(bitset.num_blocks() == num_blocks);

	const size_t old_capacity = bitset.capacity();
	bitset.clear();
	REQUIRE(bitset.empty());

	REQUIRE(bitset.capacity() == old_capacity);
}

TEMPLATE_TEST_CASE("reserve shrink_to_fit", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	const size_t size = GENERATE(
	  take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(1, 8 * bits_number<TestType>, SEED)));
	CAPTURE(size);

	dynamic_bitset<TestType> bitset;
	bitset.reserve(size);

	REQUIRE(bitset.capacity() > 0);

	bitset.shrink_to_fit();
}

TEMPLATE_TEST_CASE("is_subset_of is_proper_subset_of",
                   "[dynamic_bitset]",
                   uint16_t,
                   uint32_t,
                   uint64_t)
{
	CAPTURE(SEED);
	dynamic_bitset<TestType> bitset =
	  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
	CAPTURE(bitset);

	const dynamic_bitset<TestType> bitset_copy = bitset;

	SECTION("subset")
	{
		REQUIRE(bitset.is_subset_of(bitset_copy) == true);
		REQUIRE(bitset.is_proper_subset_of(bitset_copy) == false);
	}

	SECTION("proper subset")
	{
		if(bitset.any())
		{
			const size_t bit_to_reset =
			  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 1)))
			  % bitset.count();
			size_t bit_to_reset_pos = bitset.find_first();
			for(size_t i = 1; i < bit_to_reset; ++i)
			{
				bit_to_reset_pos = bitset.find_next(bit_to_reset_pos);
			}
			bitset.reset(bit_to_reset_pos);

			REQUIRE(bitset.is_subset_of(bitset_copy) == true);
			REQUIRE(bitset.is_proper_subset_of(bitset_copy) == true);
		}
	}

	SECTION("not a subset")
	{
		if(!bitset.all())
		{
			const dynamic_bitset<TestType> not_bitset = ~bitset;
			const size_t bit_to_set =
			  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 1)))
			  % not_bitset.count();
			size_t bit_to_set_pos = not_bitset.find_first();
			for(size_t i = 1; i < bit_to_set; ++i)
			{
				bit_to_set_pos = not_bitset.find_next(bit_to_set_pos);
			}
			bitset.set(bit_to_set_pos);

			REQUIRE(bitset.is_subset_of(bitset_copy) == false);
			REQUIRE(bitset.is_proper_subset_of(bitset_copy) == false);
		}
	}
}

TEMPLATE_TEST_CASE("intersects", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	dynamic_bitset<TestType> bitset =
	  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
	CAPTURE(bitset);

	// require non 0-only bitset
	if(bitset.none())
	{
		bitset.push_back(true);
	}

	const dynamic_bitset<TestType> bitset_copy = bitset;

	REQUIRE(bitset.intersects(bitset_copy));

	if(!bitset.all())
	{
		// flip first bit at 0
		for(size_t i = 0; i < bitset.size(); ++i)
		{
			if(bitset.test(i) == false)
			{
				bitset.flip(i);
				break;
			}
		}
		REQUIRE(bitset.intersects(bitset_copy));
	}

	bitset.flip();
	REQUIRE_FALSE(bitset.intersects(bitset_copy));
	bitset.reset();
	REQUIRE_FALSE(bitset.intersects(bitset_copy));
}

TEMPLATE_TEST_CASE("find_first find_next",
                   "[dynamic_bitset][builtin]",
                   uint16_t,
                   uint32_t,
                   uint64_t)
{
	CAPTURE(SEED);

	SECTION("empty-bitset")
	{
		dynamic_bitset<TestType> bitset;

		REQUIRE(bitset.find_first() == bitset.npos);
		REQUIRE(bitset.find_next(0) == bitset.npos);
	}

	SECTION("non-empty bitset")
	{
		const std::tuple<size_t, size_t> values =
		  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
		                     randomInt<size_t>(0, 5 * bits_number<TestType>, SEED),
		                     randomInt<size_t>(0, 5 * bits_number<TestType>, SEED + 1)));
		const size_t first_bit_pos = std::get<0>(values);
		const size_t second_bit_pos = first_bit_pos + 1 + std::get<1>(values);
		CAPTURE(first_bit_pos, second_bit_pos);

		dynamic_bitset<TestType> bitset(second_bit_pos + 12);
		REQUIRE(bitset.find_first() == bitset.npos);
		bitset.set(first_bit_pos);
		bitset.set(second_bit_pos);
		REQUIRE(bitset.find_first() == first_bit_pos);
		REQUIRE(bitset.find_next(first_bit_pos) == second_bit_pos);
		REQUIRE(bitset.find_next(second_bit_pos) == bitset.npos);
		REQUIRE(bitset.find_next(bitset.size()) == bitset.npos);
	}
}

TEMPLATE_TEST_CASE("swap", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	const std::tuple<dynamic_bitset<TestType>, dynamic_bitset<TestType>> bitsets =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomDynamicBitset<TestType>(SEED),
	                     randomDynamicBitset<TestType>(SEED + 1)));
	dynamic_bitset<TestType> bitset1 = std::get<0>(bitsets);
	dynamic_bitset<TestType> bitset2 = std::get<1>(bitsets);
	CAPTURE(bitset1, bitset2);

	SECTION("member function")
	{
		const dynamic_bitset<TestType> bitset1_copy = bitset1;
		const dynamic_bitset<TestType> bitset2_copy = bitset2;
		bitset1.swap(bitset2);
		REQUIRE(bitset1 == bitset2_copy);
		REQUIRE(bitset2 == bitset1_copy);
	}

	SECTION("external function")
	{
		const dynamic_bitset<TestType> bitset1_copy = bitset1;
		const dynamic_bitset<TestType> bitset2_copy = bitset2;
		swap(bitset1, bitset2);
		REQUIRE(bitset1 == bitset2_copy);
		REQUIRE(bitset2 == bitset1_copy);
	}
}

TEMPLATE_TEST_CASE("get_allocator", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	dynamic_bitset<TestType> bitset;
	static_cast<void>(bitset.get_allocator()); // avoid unused warnings
}

TEMPLATE_TEST_CASE("to_string", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	const std::tuple<unsigned long long, size_t> values =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomInt<unsigned long long>(SEED),
	                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1)));
	unsigned long long value = std::get<0>(values);
	const size_t bits_to_take = std::get<1>(values);
	CAPTURE(value, bits_to_take);

	dynamic_bitset<TestType> bitset(bits_to_take, value);
	CAPTURE(bitset);

	std::string string;
	string.reserve(bits_to_take);
	for(size_t i = bits_to_take - 1; i > 0; --i)
	{
		string.push_back(bit_value(value, i) ? '1' : '0');
	}
	string.push_back(bit_value(value, 0) ? '1' : '0');

	REQUIRE(bitset.to_string() == string);
}

TEMPLATE_TEST_CASE("iterate_bits_on", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	const std::tuple<unsigned long long, size_t> values =
	  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
	                     randomInt<unsigned long long>(SEED),
	                     randomInt<size_t>(1, bits_number<unsigned long long>, SEED + 1)));
	unsigned long long value = std::get<0>(values);
	const size_t bits_to_take = std::get<1>(values);
	CAPTURE(value, bits_to_take);

	dynamic_bitset<TestType> bitset(bits_to_take, value);
	CAPTURE(bitset);

	SECTION("return void")
	{
		SECTION("no parameters")
		{
			size_t current_check_bit = 0;
			bitset.iterate_bits_on([&](size_t bit_pos) {
				while(current_check_bit < bit_pos)
				{
					REQUIRE(bitset[current_check_bit] == false);
					++current_check_bit;
				}
				REQUIRE(bitset[bit_pos] == true);
				++current_check_bit;
			});
			for(size_t i = current_check_bit; i < bits_to_take; ++i)
			{
				REQUIRE(bitset[i] == false);
			}
		}

		SECTION("parameters")
		{
			dynamic_bitset<TestType> check_bitset(bits_to_take);
			bitset.iterate_bits_on(
			  [](size_t bit_pos, dynamic_bitset<TestType>& check_bitset_) {
				  check_bitset_[bit_pos] = true;
			  },
			  check_bitset);
			REQUIRE(check_bitset == bitset);
		}
	}

	SECTION("return bool")
	{
		if(bitset.count() == 0)
		{
			bitset.push_back(true);
		}
		const size_t stop_at_bit =
		  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 2))) % bitset.count()
		  + 1;

		SECTION("no parameters")
		{
			size_t current_check_bit = 0;
			size_t bit_count = 0;
			bitset.iterate_bits_on([&](size_t bit_pos) {
				while(current_check_bit < bit_pos)
				{
					REQUIRE(bitset[current_check_bit] == false);
					++current_check_bit;
				}
				REQUIRE(bitset[bit_pos] == true);
				++current_check_bit;

				++bit_count;
				return bit_count < stop_at_bit;
			});
			REQUIRE(bit_count == stop_at_bit);
		}

		SECTION("parameters")
		{
			size_t bit_count = 0;
			size_t last_bit_pos = 0;
			dynamic_bitset<TestType> check_bitset(bitset.size());
			bitset.iterate_bits_on(
			  [](size_t bit_pos,
			     dynamic_bitset<TestType>& check_bitset_,
			     size_t& bit_count_,
			     size_t& last_bit_pos_,
			     const size_t stop_at_bit_) {
				  check_bitset_[bit_pos] = true;
				  last_bit_pos_ = bit_pos;

				  ++bit_count_;
				  return bit_count_ < stop_at_bit_;
			  },
			  check_bitset,
			  bit_count,
			  last_bit_pos,
			  stop_at_bit);
			REQUIRE(bit_count == stop_at_bit);

			check_bitset.resize(last_bit_pos);
			bitset.resize(last_bit_pos);
			REQUIRE(check_bitset == bitset);
		}
	}
}

TEMPLATE_TEST_CASE("operator== operator!=", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	dynamic_bitset<TestType> bitset =
	  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
	CAPTURE(bitset);

	SECTION("same")
	{
		const dynamic_bitset<TestType> bitset_copy = bitset;
		REQUIRE(bitset == bitset_copy);
		REQUIRE_FALSE(bitset != bitset_copy);
	}

	SECTION("different size and same bits")
	{
		const dynamic_bitset<TestType> bitset_copy = bitset;
		bitset.push_back(true);
		REQUIRE_FALSE(bitset == bitset_copy);
		REQUIRE_FALSE(bitset_copy == bitset);
		REQUIRE(bitset != bitset_copy);
		REQUIRE(bitset_copy != bitset);
	}

	SECTION("same size and different bits")
	{
		if(bitset.empty())
		{
			bitset.push_back(true);
		}
		const dynamic_bitset<TestType> bitset_copy = bitset;

		size_t pos =
		  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 1))) % bitset.size();
		CAPTURE(pos);
		bitset.flip(pos);
		REQUIRE_FALSE(bitset == bitset_copy);
		REQUIRE_FALSE(bitset_copy == bitset);
		REQUIRE(bitset != bitset_copy);
		REQUIRE(bitset_copy != bitset);
	}
}

TEMPLATE_TEST_CASE("operator< operator<= operator> operator>=",
                   "[dynamic_bitset]",
                   uint16_t,
                   uint32_t,
                   uint64_t)
{
	CAPTURE(SEED);

	SECTION("2 empty bitsets")
	{
		const dynamic_bitset<TestType> bitset1;
		const dynamic_bitset<TestType> bitset2;

		REQUIRE_FALSE(bitset1 < bitset2);
		REQUIRE_FALSE(bitset2 < bitset1);
		REQUIRE(bitset1 <= bitset2);
		REQUIRE(bitset2 <= bitset1);

		REQUIRE_FALSE(bitset1 > bitset2);
		REQUIRE_FALSE(bitset2 > bitset1);
		REQUIRE(bitset1 >= bitset2);
		REQUIRE(bitset2 >= bitset1);
	}

	SECTION("1 empty bitset")
	{
		const dynamic_bitset<TestType> bitset =
		  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
		const dynamic_bitset<TestType> empty_bitset;
		CAPTURE(bitset);

		REQUIRE(empty_bitset < bitset);
		REQUIRE_FALSE(bitset < empty_bitset);
		REQUIRE(empty_bitset <= bitset);
		REQUIRE_FALSE(bitset <= empty_bitset);

		REQUIRE_FALSE(empty_bitset > bitset);
		REQUIRE(bitset > empty_bitset);
		REQUIRE_FALSE(empty_bitset >= bitset);
		REQUIRE(bitset >= empty_bitset);
	}

	SECTION("non-empty bitsets")
	{
		const std::tuple<unsigned long long, unsigned long long> values =
		  GENERATE(multitake(RANDOM_VECTORS_TO_TEST,
		                     randomInt<unsigned long long>(SEED),
		                     randomInt<unsigned long long>(SEED + 1)));
		const unsigned long long value1 = std::get<0>(values);
		const unsigned long long value2 = std::get<1>(values) % value1; // value2 != value1
		const size_t bits_to_take = bits_number<unsigned long long>;
		CAPTURE(value1, value2, bits_to_take);

		SECTION("same")
		{
			const dynamic_bitset<TestType> bitset1(bits_to_take, value1);
			const dynamic_bitset<TestType> bitset2(bits_to_take, value1);

			REQUIRE_FALSE(bitset1 < bitset2);
			REQUIRE_FALSE(bitset2 < bitset1);
			REQUIRE(bitset1 <= bitset2);
			REQUIRE(bitset2 <= bitset1);

			REQUIRE_FALSE(bitset1 > bitset2);
			REQUIRE_FALSE(bitset2 > bitset1);
			REQUIRE(bitset1 >= bitset2);
			REQUIRE(bitset2 >= bitset1);
		}

		SECTION("different size and same bits")
		{
			const dynamic_bitset<TestType> bitset1(bits_to_take, value1);
			dynamic_bitset<TestType> bitset2(bits_to_take, value1);
			const bool added_value = GENERATE(true, false);
			CAPTURE(added_value);
			bitset2.push_back(added_value);

			REQUIRE(bitset1 < bitset2);
			REQUIRE_FALSE(bitset2 < bitset1);
			REQUIRE(bitset1 <= bitset2);
			REQUIRE_FALSE(bitset2 <= bitset1);

			REQUIRE_FALSE(bitset1 > bitset2);
			REQUIRE(bitset2 > bitset1);
			REQUIRE_FALSE(bitset1 >= bitset2);
			REQUIRE(bitset2 >= bitset1);
		}

		SECTION("same size and different bits")
		{
			const dynamic_bitset<TestType> bitset1(bits_to_take, value1);
			const dynamic_bitset<TestType> bitset2(bits_to_take, value2);
			if(value1 < value2)
			{
				REQUIRE(bitset1 < bitset2);
				REQUIRE_FALSE(bitset2 < bitset1);
				REQUIRE(bitset1 <= bitset2);
				REQUIRE_FALSE(bitset2 <= bitset1);

				REQUIRE_FALSE(bitset1 > bitset2);
				REQUIRE(bitset2 > bitset1);
				REQUIRE_FALSE(bitset1 >= bitset2);
				REQUIRE(bitset2 >= bitset1);
			}
			else
			{
				REQUIRE(bitset2 < bitset1);
				REQUIRE_FALSE(bitset1 < bitset2);
				REQUIRE(bitset2 <= bitset1);
				REQUIRE_FALSE(bitset1 <= bitset2);

				REQUIRE_FALSE(bitset2 > bitset1);
				REQUIRE(bitset1 > bitset2);
				REQUIRE_FALSE(bitset2 >= bitset1);
				REQUIRE(bitset1 >= bitset2);
			}
		}

		SECTION("different size and different bits")
		{
			SECTION("difference in common blocks")
			{
				dynamic_bitset<TestType> bitset1(bits_to_take, value1);
				dynamic_bitset<TestType> bitset2(bits_to_take, value1);

				// make bitset1 < bitset2
				const size_t bit_pos =
				  GENERATE(take(RANDOM_VARIATIONS_TO_TEST, randomInt<size_t>(SEED + 2)))
				  % bitset1.size();
				CAPTURE(bit_pos);
				if(bitset1[bit_pos])
				{
					bitset1.reset(bit_pos);
				}
				else
				{
					bitset2.set(bit_pos);
				}

				// add some 0 to a bitset to have a different size
				const size_t bits_to_add =
				  GENERATE(take(RANDOM_VARIATIONS_TO_TEST,
				                randomInt<size_t>(0, 2 * bits_number<TestType>, SEED + 3)));
				const bool bitset_to_add = GENERATE(true, false);
				CAPTURE(bits_to_add, bitset_to_add);

				dynamic_bitset<TestType>& longest_bitset = bitset_to_add ? bitset1 : bitset2;
				for(size_t i = 0; i < bits_to_add; ++i)
				{
					longest_bitset.push_back(false);
				}

				REQUIRE(bitset1 < bitset2);
				REQUIRE_FALSE(bitset2 < bitset1);
				REQUIRE(bitset1 <= bitset2);
				REQUIRE_FALSE(bitset2 <= bitset1);

				REQUIRE_FALSE(bitset1 > bitset2);
				REQUIRE(bitset2 > bitset1);
				REQUIRE_FALSE(bitset1 >= bitset2);
				REQUIRE(bitset2 >= bitset1);
			}

			SECTION("difference in extra blocks")
			{
				dynamic_bitset<TestType> longest_bitset(bits_to_take, value1);
				dynamic_bitset<TestType> bitset(bits_to_take, value1);

				dynamic_bitset<TestType> bits_to_add =
				  GENERATE(take(RANDOM_VARIATIONS_TO_TEST,
				                randomDynamicBitset<TestType>(1, 2 * bits_number<TestType>, SEED)));
				CAPTURE(bits_to_add);
				if(bits_to_add.none())
				{
					bits_to_add.set(0);
				}
				for(size_t i = 0; i < bits_to_add.size(); ++i)
				{
					longest_bitset.push_back(longest_bitset[i]);
				}

				REQUIRE(bitset < longest_bitset);
				REQUIRE_FALSE(longest_bitset < bitset);
				REQUIRE(bitset <= longest_bitset);
				REQUIRE_FALSE(longest_bitset <= bitset);

				REQUIRE_FALSE(bitset > longest_bitset);
				REQUIRE(longest_bitset > bitset);
				REQUIRE_FALSE(bitset >= longest_bitset);
				REQUIRE(longest_bitset >= bitset);
			}
		}
	}
}

TEMPLATE_TEST_CASE("ostream operator<<", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);
	dynamic_bitset<TestType> bitset =
	  GENERATE(take(RANDOM_VECTORS_TO_TEST, randomDynamicBitset<TestType>(SEED)));
	CAPTURE(bitset);

	std::stringstream sstream;
	sstream << bitset;
	std::string str = sstream.str();
	CAPTURE(str);

	REQUIRE(str.size() == bitset.size());
	for(size_t i = 0; i < bitset.size(); ++i)
	{
		CAPTURE(i);
		if(bitset[bitset.size() - i - 1])
		{
			REQUIRE(str[i] == '1');
		}
		else
		{
			REQUIRE(str[i] == '0');
		}
	}
}

TEMPLATE_TEST_CASE("istream operator>>", "[dynamic_bitset]", uint16_t, uint32_t, uint64_t)
{
	CAPTURE(SEED);

	SECTION("invalid stream")
	{
		std::stringstream sstream;
		dynamic_bitset<TestType> bitset;
		sstream >> bitset;
		REQUIRE(bitset.empty());
	}

	SECTION("valid stream")
	{
		SECTION("only valid characters")
		{
			std::string str = GENERATE(take(RANDOM_VECTORS_TO_TEST, randomBitsetString(SEED)));
			CAPTURE(str);

			std::stringstream sstream;
			sstream.str(str);
			dynamic_bitset<TestType> bitset;
			sstream >> bitset;
			CAPTURE(bitset);

			REQUIRE(bitset.size() == str.size());
			for(size_t i = 0; i < str.size(); ++i)
			{
				CAPTURE(i);
				if(str[str.size() - i - 1] == '1')
				{
					REQUIRE(bitset.test(i));
				}
				else
				{
					REQUIRE_FALSE(bitset.test(i));
				}
			}
			REQUIRE(sstream.eof());
		}

		SECTION("with invalid characters")
		{
			std::string str = GENERATE(take(RANDOM_VECTORS_TO_TEST, randomBitsetString(SEED)));
			CAPTURE(str);

			std::stringstream sstream;
			sstream << str;
			sstream << 'E';
			dynamic_bitset<TestType> bitset;
			sstream >> bitset;
			CAPTURE(bitset);

			REQUIRE(bitset.size() == str.size());
			for(size_t i = 0; i < str.size(); ++i)
			{
				CAPTURE(i);
				if(str[str.size() - i - 1] == '1')
				{
					REQUIRE(bitset.test(i));
				}
				else
				{
					REQUIRE_FALSE(bitset.test(i));
				}
			}
			char E;
			sstream >> E;
			REQUIRE(E == 'E');
			sstream >> E;
			REQUIRE(sstream.eof());
		}
	}
}
