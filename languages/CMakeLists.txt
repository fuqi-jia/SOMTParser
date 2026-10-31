# One static library for all languages. Core never depends on this target, so
# linking only somtparser keeps SMT-LIB working with no extra size or build cost.

file(GLOB SOMTPARSER_LANGUAGE_DIRS RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}"
     CONFIGURE_DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/*")

set(SOMTPARSER_LANGUAGE_SOURCES
    "${CMAKE_CURRENT_SOURCE_DIR}/register_all.cpp")

foreach(dir IN LISTS SOMTPARSER_LANGUAGE_DIRS)
    if(NOT IS_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/${dir}")
        continue()
    endif()
    if(dir MATCHES "^_")           # _template and friends are not built
        continue()
    endif()
    file(GLOB_RECURSE lang_src CONFIGURE_DEPENDS
         "${CMAKE_CURRENT_SOURCE_DIR}/${dir}/src/*.cpp")
    list(APPEND SOMTPARSER_LANGUAGE_SOURCES ${lang_src})
endforeach()

add_library(somtparser_languages ${SOMTPARSER_LANGUAGE_SOURCES})
add_library(SOMTParser::languages ALIAS somtparser_languages)
target_compile_features(somtparser_languages PUBLIC cxx_std_17)
set_target_properties(somtparser_languages PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_link_libraries(somtparser_languages PUBLIC SOMTParser::somtparser)

# Language headers are reached as <somtparser/languages/<lang>.h>; the shim
# directory below maps that onto the per-language folders.
target_include_directories(somtparser_languages PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/include>
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>)

file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/include/somtparser/languages")
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/register_all.h"
               "${CMAKE_CURRENT_BINARY_DIR}/include/somtparser/languages/register_all.h"
               COPYONLY)
# Each language publishes exactly one header, named after its directory, and it
# is reached as <somtparser/languages/<lang>.h>. Derived from the same glob the
# sources use rather than listed by hand: a hand-written list is a per-language
# step that is easy to forget, and forgetting it fails at compile time with a
# missing header rather than with anything that names the real cause.
foreach(dir IN LISTS SOMTPARSER_LANGUAGE_DIRS)
    if(NOT IS_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/${dir}")
        continue()
    endif()
    if(dir MATCHES "^_")
        continue()
    endif()
    if(NOT EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${dir}/${dir}.h")
        message(FATAL_ERROR
            "language '${dir}' has no ${dir}/${dir}.h; every language publishes one "
            "header named after its directory")
    endif()
    configure_file("${CMAKE_CURRENT_SOURCE_DIR}/${dir}/${dir}.h"
                   "${CMAKE_CURRENT_BINARY_DIR}/include/somtparser/languages/${dir}.h"
                   COPYONLY)
endforeach()

install(TARGETS somtparser_languages
    EXPORT SOMTParserTargets
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})
install(DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/include/somtparser"
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
    FILES_MATCHING PATTERN "*.h")

# Language tests live in test/languages/, with every other test, and are built
# by test/CMakeLists.txt. This directory used to run a second, parallel copy of
# that foreach -- its own executables, its own -UNDEBUG handling, its own
# add_test -- which meant two places to keep in step and two places to look for
# a test. Sources and instances stay per-language because they are the
# language; the tests are just tests.
