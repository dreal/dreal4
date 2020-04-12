//
// Copyright (c) 2019 Maxime Pinard
//
// Distributed under the MIT license
// See accompanying file LICENSE or copy at
// https://opensource.org/licenses/MIT
//
#include <dynamic_bitset.hpp>

#include <iostream>

int main()
{
	std::cout << std::boolalpha;

	// declare bitset with 12 bits from a value
	dynamic_bitset<uint32_t> a(12, 0b0100010110111);

	// remove all bits, resize to 0
	a.clear();

	// add a bit at 1 to the end of the bitset
	a.push_back(true);

	// remove last bit if not empty
	a.pop_back();

	// append a full block to the bitset (including the leftmost leading 0s)
	// in this case append 32 bits
	a.append(314153u);

	// same as above with multiple blocks
	a.append({112u, 5146u, 546u});

	// resize the bitset, keep 12 first bits, discard others
	a.resize(12);

	// set bits 3 to 7 to 1
	a.set(3, 4, true);

	// set bit 2 to 0
	a.set(2, false);

	// set bit 1 to 1
	a.set(1);

	// set all bits to 1
	a.set();

	// reset bits 4 to 9 to 0
	a.reset(4, 5);

	// reset bit 8 to 0
	a.reset(8);

	// reset all bits to 0
	a.reset();

	// flip bits 5 to 8
	a.flip(5, 3);

	// flip bit 2
	a.flip(2);

	// flip all bits
	a.flip();

	std::cout << "a = " << a << std::endl;

	// test the value of bit 2
	std::cout << "Bit 2 is on? " << a.test(2) << std::endl;

	// test bit 4 and set it to 0
	std::cout << "Bit 4 is on? " << a.test_set(4, false) << " (set it to 0)" << std::endl;
	std::cout << "a = " << a << std::endl;

	// test bit 7 and set it to 1
	std::cout << "Bit 7 is on? " << a.test_set(7) << " (set it to 1)" << std::endl;
	std::cout << "a = " << a << std::endl;

	// test if the bitset is empty
	std::cout << "Is the bitset empty? " << a.empty() << std::endl;

	// get bitset size
	std::cout << "Bitset size: " << a.size() << std::endl;

	// test if all bits are 1
	std::cout << "All bits are on? " << a.all() << std::endl;

	// test if there is at least one bit at 1
	std::cout << "Any bits are on? " << a.any() << std::endl;

	// test if all bits are 0
	std::cout << "All bits are off? " << a.none() << std::endl;

	// count bits to 1
	std::cout << "Number of bits on: " << a.count() << std::endl;

	// get number of blocks used by the bitset
	std::cout << "Number of blocks used by the bitset: " << a.num_blocks() << std::endl;

	// get bitset capacity
	std::cout << "Bitset capacity: " << a.capacity() << std::endl;

	// find position of the first bit to 1
	const size_t pos = a.find_first();
	std::cout << "First bit on position: " << pos << std::endl;

	// find position of the next bit to 1
	std::cout << "Second bit on position: " << a.find_next(pos) << std::endl;

	// conversion to string with . and *
	std::cout << "String representation (. and *): " << a.to_string('.', '*') << std::endl;

	// conversion to string with 0 and 1
	std::cout << "String representation (0 and 1): " << a.to_string() << std::endl;

	// iterate on bits on
	std::cout << "Bits on: ";
	a.iterate_bits_on([](size_t bit_pos) noexcept { std::cout << bit_pos << ' '; });
	std::cout << std::endl;
	// (it is possible to pass parameters and return a 'continue' bool)
	size_t bit_counter = 0;
	std::cout << "3 first bits on: ";
	a.iterate_bits_on(
	  [&bit_counter](size_t bit_pos, size_t limit) noexcept {
		  std::cout << bit_pos << ' ';
		  return ++bit_counter < limit;
	  },
	  3);
	std::cout << std::endl;

	// reserve 64 bits
	a.reserve(64);

	// requests the removal of unused capacity
	a.shrink_to_fit();

	// get allocator
	const dynamic_bitset<uint32_t>::allocator_type allocator = a.get_allocator();

	// declare bitset from string
	dynamic_bitset<uint32_t> b("011001010101");
	std::cout << "b = " << b << std::endl;

	// determine if a bitset is a subset of another bitset
	// (if it only contain bits from the other bitset)
	std::cout << "a is a subset of b? " << a.is_subset_of(b) << std::endl;

	// determine if a bitset is a proper subset of another bitset
	// (if it is different and only contain bits from the other bitset)
	std::cout << "a is a proper subset of b? " << a.is_proper_subset_of(b) << std::endl;

	// determine if a bitset intersect another bitset
	// (if they have common bits to 1)
	std::cout << "Does a intersect b? " << a.intersects(b) << std::endl;

	// operators
	std::cout << "~a: " << ~a << std::endl;
	std::cout << "a << 3: " << (a << 3) << std::endl;
	std::cout << "a >> 3: " << (a >> 3) << std::endl;
	std::cout << "a & b: " << (a & b) << std::endl;
	std::cout << "a | b: " << (a | b) << std::endl;
	std::cout << "a ^ b: " << (a ^ b) << std::endl;
	std::cout << "a - b: " << (a - b) << std::endl;
	std::cout << "a == b: " << (a == b) << std::endl;
	std::cout << "a < b: " << (a < b) << std::endl;

	// operator[] access
	std::cout << "a[3]: " << a[3] << std::endl;
	std::cout << "~a[3]: " << ~a[3] << std::endl;
	a[3] = false;
	a[3].set();
	a[3].reset();
	a[3].flip();
	a[3].assign(true);
	a[3] = a[2];
	a[3] &= a[2];
	a[3] |= a[2];
	a[3] ^= a[2];
	a[3] -= a[2];

	return 0;
}
