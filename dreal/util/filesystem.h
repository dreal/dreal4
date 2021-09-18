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
#pragma once

#include <sys/stat.h>

#include <string>

namespace dreal {

/// Returns true if a filename @p name exists.
bool file_exists(const std::string& name);

/// Extracts the extension from @p name.
///
/// @note It returns an empty string if there is no extension in @p name.
std::string get_extension(const std::string& name);

}  // namespace dreal
