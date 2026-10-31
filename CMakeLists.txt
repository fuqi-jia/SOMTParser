cmake_minimum_required(VERSION 3.16)
project(SOMTParser VERSION 1.0.0 LANGUAGES CXX)

include(CTest)
include(CMakePackageConfigHelpers)
include(GNUInstallDirs)

list(PREPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

option(SOMTPARSER_BUILD_TESTS "Build SOMTParser tests" OFF)
option(SOMTPARSER_WARNINGS_AS_ERRORS "Treat SOMTParser warnings as errors" OFF)
option(SOMTPARSER_ENABLE_TIMING "Enable the timing profiler" OFF)
option(BUILD_PYTHON "Build the Python bindings module" OFF)
option(SOMTPARSER_BUILD_LANGUAGES "Build the multi-language frontend library" ON)
option(SOMTPARSER_BUILD_TOOLS "Build command line tools" OFF)

# Apply to every project target (core, languages, tools, tests and bindings),
# without exporting compiler policy to applications linking the library.
if(SOMTPARSER_WARNINGS_AS_ERRORS)
    if(MSVC)
        add_compile_options(/WX)
    elseif(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
        add_compile_options(-Werror)
    endif()
endif()

if(PROJECT_IS_TOP_LEVEL AND NOT CMAKE_CONFIGURATION_TYPES AND NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS Debug Release RelWithDebInfo MinSizeRel)
endif()

find_package(GMP REQUIRED)
find_package(MPFR REQUIRED)

file(GLOB_RECURSE SOMTPARSER_SOURCES CONFIGURE_DEPENDS "src/*.cpp")
file(GLOB_RECURSE SOMTPARSER_HEADERS CONFIGURE_DEPENDS "include/somtparser/*.h")

# The IR/numeric library is independently linkable. Compile these objects once.
set(SOMTPARSER_IR_SOURCES
    src/core/kind.cpp src/core/util.cpp
    src/ir/dag.cpp src/ir/sort.cpp src/ir/number.cpp
    src/ir/interval.cpp src/ir/value.cpp)
foreach(source IN LISTS SOMTPARSER_IR_SOURCES)
    list(REMOVE_ITEM SOMTPARSER_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/${source}")
endforeach()
add_library(somtparser_ir_objects OBJECT ${SOMTPARSER_IR_SOURCES})
set_target_properties(somtparser_ir_objects PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_compile_features(somtparser_ir_objects PUBLIC cxx_std_17)
target_include_directories(somtparser_ir_objects PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)
target_link_libraries(somtparser_ir_objects PUBLIC GMP::GMPXX MPFR::MPFR)
add_library(somtparser_ir STATIC $<TARGET_OBJECTS:somtparser_ir_objects>)
add_library(SOMTParser::somtparser_ir ALIAS somtparser_ir)
target_compile_features(somtparser_ir PUBLIC cxx_std_17)
target_include_directories(somtparser_ir PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>)
target_link_libraries(somtparser_ir PUBLIC GMP::GMPXX MPFR::MPFR)
list(APPEND SOMTPARSER_SOURCES $<TARGET_OBJECTS:somtparser_ir_objects>)

add_library(somtparser ${SOMTPARSER_SOURCES} ${SOMTPARSER_HEADERS})
add_library(SOMTParser::somtparser ALIAS somtparser)
set_target_properties(somtparser PROPERTIES
    EXPORT_NAME somtparser
    POSITION_INDEPENDENT_CODE ON)
target_compile_features(somtparser PUBLIC cxx_std_17)
target_include_directories(somtparser PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>)
target_link_libraries(somtparser PUBLIC GMP::GMPXX MPFR::MPFR)

if(SOMTPARSER_ENABLE_TIMING)
    target_compile_definitions(somtparser PUBLIC ENABLE_TIMING)
    target_compile_definitions(somtparser_ir_objects PUBLIC ENABLE_TIMING)
    target_compile_definitions(somtparser_ir PUBLIC ENABLE_TIMING)
endif()

if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    target_compile_options(somtparser PRIVATE
        -Wall
        -Wextra
        -Wpedantic
        -Wno-unused-parameter
        -Wno-unused-variable
        -Wno-unused-function
        -Wno-unused-but-set-variable
        -Wno-unused-value
        -Wno-unused-local-typedefs)
endif()

if(SOMTPARSER_BUILD_LANGUAGES)
    add_subdirectory(languages)
endif()

if(SOMTPARSER_BUILD_TOOLS AND SOMTPARSER_BUILD_LANGUAGES)
    add_subdirectory(tools)
endif()

if(SOMTPARSER_BUILD_TESTS)
    enable_testing()
    add_subdirectory(test)
endif()

install(TARGETS somtparser somtparser_ir
    EXPORT SOMTParserTargets
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
    INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
install(DIRECTORY include/somtparser
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
    FILES_MATCHING PATTERN "*.h")
install(EXPORT SOMTParserTargets
    FILE SOMTParserTargets.cmake
    NAMESPACE SOMTParser::
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/SOMTParser)

configure_package_config_file(
    cmake/SOMTParserConfig.cmake.in
    ${CMAKE_CURRENT_BINARY_DIR}/SOMTParserConfig.cmake
    INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/SOMTParser)
write_basic_package_version_file(
    ${CMAKE_CURRENT_BINARY_DIR}/SOMTParserConfigVersion.cmake
    VERSION ${PROJECT_VERSION}
    COMPATIBILITY SameMajorVersion)
install(FILES
    ${CMAKE_CURRENT_BINARY_DIR}/SOMTParserConfig.cmake
    ${CMAKE_CURRENT_BINARY_DIR}/SOMTParserConfigVersion.cmake
    cmake/FindGMP.cmake
    cmake/FindMPFR.cmake
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/SOMTParser)

if(BUILD_PYTHON)
    # The Python module is not core-only: python/bindings.cpp includes
    # <somtparser/languages/register_all.h>, a header that exists solely in the
    # languages target's binary include dir, and python/somtparser/__init__.py
    # unconditionally imports translate/languages/profiles/coverage. There is no
    # build flavour of the package that advertises less, so a module built
    # without languages would either fail to compile or import an API backed by
    # an empty language registry. Reject the combination here rather than let it
    # fail deep in a build log or, worse, at runtime.
    if(NOT SOMTPARSER_BUILD_LANGUAGES)
        message(FATAL_ERROR
            "BUILD_PYTHON=ON requires SOMTPARSER_BUILD_LANGUAGES=ON: the Python "
            "module exposes the multi-language frontend API "
            "(somtparser.translate / languages / profiles / coverage) and "
            "includes <somtparser/languages/register_all.h>, which only the "
            "languages target generates.")
    endif()
    find_package(Python 3.9 REQUIRED COMPONENTS Interpreter Development.Module)
    find_package(pybind11 CONFIG REQUIRED)
    # Keep registration templates in separate translation units. Combining all
    # API families in one unit makes compiler memory grow with the entire API.
    # NO_EXTRAS disables pybind11's automatic LTO for this wrapper module only.
    pybind11_add_module(_somtparser NO_EXTRAS
        python/bindings.cpp
        python/translate_bindings.cpp
        python/hir_bindings.cpp
        python/planning_numeric_bindings.cpp
        python/planning_trajectory_bindings.cpp
        python/planning_derived_bindings.cpp
        python/planning_temporal_bindings.cpp
        python/planning_timed_initial_bindings.cpp
        python/planning_continuous_bindings.cpp
        python/planning_objects_bindings.cpp
        python/module_bindings.cpp
    )
    set_property(TARGET _somtparser PROPERTY INTERPROCEDURAL_OPTIMIZATION FALSE)
    # pybind11 registration templates can exceed COFF's 65,279-section limit
    # even with bindings split into translation units. Use extended objects on
    # MSVC; this changes object storage, not warning policy or generated APIs.
    if(MSVC)
        target_compile_options(_somtparser PRIVATE /bigobj)
    endif()
    # Numeric/frontend execution remains in the normally optimized core and
    # language libraries; aggressive optimization of registration glue is costly.
    target_compile_options(_somtparser PRIVATE
        $<$<AND:$<CONFIG:Release>,$<CXX_COMPILER_ID:GNU,Clang,AppleClang>>:-O1>)
    target_link_libraries(_somtparser PRIVATE SOMTParser::languages)
    install(TARGETS _somtparser LIBRARY DESTINATION . COMPONENT Python)
endif()
