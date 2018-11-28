#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/container/inlined_vector.h"

int main() {
  // Simply checks if we can have absl containers.
  { absl::flat_hash_map<int, int> map; }
  { absl::flat_hash_set<int> set; }
  { absl::InlinedVector<int, 20> vector; }
}
