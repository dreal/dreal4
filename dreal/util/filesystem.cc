#include "dreal/util/filesystem.h"

namespace dreal {

using std::string;

bool file_exists(const string& name) {
  struct stat buffer;  // NOLINT
  if (stat(name.c_str(), &buffer) != 0) {
    return false;
  }
  return S_ISREG(buffer.st_mode);
}

string get_extension(const string& name) {
  const auto idx = name.rfind('.');
  if (idx != string::npos) {
    return name.substr(idx + 1);
  } else {
    // No extension found
    return "";
  }
}
}  // namespace dreal
