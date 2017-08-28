#include "spdlog/spdlog.h"
#include <iostream>

int main(int, char* []) {
  // Multithreaded console logger(with color support)
  auto console = spdlog::stdout_color_mt("console");
  console->info("Welcome to spdlog!");
  console->info("An info message example {}..", 1);

  try {
    // Create basic file logger (not rotated)
    auto my_logger = spdlog::basic_logger_mt("basic_logger", "logs/basic.txt");

    // create a file rotating logger with 5mb size max and 3 rotated files
    auto file_logger = spdlog::rotating_logger_mt("file_logger", "myfilename",
                                                  1024 * 1024 * 5, 3);
  } catch (const spdlog::spdlog_ex& ex) {
    std::cout << "Log initialization failed: " << ex.what() << std::endl;
  }
}
