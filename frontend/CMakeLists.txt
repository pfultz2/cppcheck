file(GLOB hdrs "*.h")
file(GLOB srcs "*.cpp")

cppcheck_add_library(frontend ${hdrs} ${srcs})
target_include_directories(frontend PUBLIC .)
target_link_libraries(frontend PRIVATE cppcheck-core)
