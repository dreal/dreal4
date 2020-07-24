#include <iostream>

#include <gmpxx.h>

// We merely check that we can compile code which is using GMP.
int main() {
  const mpq_class r{3.141592};
  std::cerr << r << std::endl;
  std::cerr << "(/" << r.get_num() << " " << r.get_den() << ")" << std::endl;
}
