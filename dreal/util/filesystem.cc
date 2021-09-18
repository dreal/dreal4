/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
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
