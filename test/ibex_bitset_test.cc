#include "./ibex.h"

#include <iostream>

#include <gtest/gtest.h>

namespace {

using std::endl;
using std::cerr;

GTEST_TEST(IbexBitsetTest, Add) {
  // TODO(soonho): add.
  int _bitset1[3] = {3, 7, 161};
  int _bitset2[2] = {4, 7};
  int _bitset3[4] = {3, 4, 7, 160};
  ibex::BitSet bitset1(3, _bitset1);
  ibex::BitSet bitset2(2, _bitset2);
  ibex::BitSet bitset3(4, _bitset3);

  ibex::BitSet bs;

  cerr << bitset1.max() << endl;
  cerr << bitset2.max() << endl;
  cerr << bitset3.max() << endl;

  bs.display(cerr);
  cerr << endl;

  bs.display(cerr);
  cerr << endl;

  bs.union_with(bitset1);
  bs.union_with(bitset2);
  bs.union_with(bitset3);

  bs.display(cerr);
  cerr << endl;
}

}  // namespace
