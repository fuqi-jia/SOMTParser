file(GLOB_RECURSE SOMTPARSER_TEST_SOURCES CONFIGURE_DEPENDS "*.cpp")

# test/languages/ needs the language frontends, which are an optional component
# (SOMTPARSER_BUILD_LANGUAGES). Drop those tests rather than fail the configure
# when they are not built -- a core-only build is a supported configuration, and
# every other test here runs in it unchanged.
if(NOT TARGET SOMTParser::languages)
    list(FILTER SOMTPARSER_TEST_SOURCES
         EXCLUDE REGEX "^${CMAKE_CURRENT_SOURCE_DIR}/languages/")
endif()

set(SOMTPARSER_TEST_TARGETS)
foreach(test_file IN LISTS SOMTPARSER_TEST_SOURCES)
    get_filename_component(test_name "${test_file}" NAME_WE)
    list(APPEND SOMTPARSER_TEST_TARGETS "${test_name}")

    add_executable("${test_name}" "${test_file}")
    target_compile_features("${test_name}" PRIVATE cxx_std_17)
    target_include_directories("${test_name}" PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}")
    # Linked to every test, not only to test/languages/. The languages archive
    # carries somtparser as a PUBLIC dependency, so this is the same core
    # library either way, and a per-directory rule would be one more thing to
    # get right when a test moves between directories.
    if(TARGET SOMTParser::languages)
        target_link_libraries("${test_name}" PRIVATE SOMTParser::languages)
    else()
        target_link_libraries("${test_name}" PRIVATE SOMTParser::somtparser)
    endif()

    # A test must verify its expectations in every configuration. The default
    # top-level build type is Release, which defines NDEBUG and so turns every
    # assert() into a no-op -- including any whose expression does the work
    # being tested. Tests use VERIFY from test_helpers.h, but undefine NDEBUG
    # here as well so a stray assert() cannot silently stop checking. No
    # library header is NDEBUG-conditional, so this cannot cause an ODR
    # mismatch with libsomtparser.
    if(MSVC)
        target_compile_options("${test_name}" PRIVATE /UNDEBUG)
    else()
        target_compile_options("${test_name}" PRIVATE -UNDEBUG)
    endif()

    add_test(NAME "SOMTParser.${test_name}" COMMAND "${test_name}")
    set_tests_properties("SOMTParser.${test_name}" PROPERTIES
        WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}")
    # This test compares CPU scaling, so concurrent suite workloads can distort
    # its cache/memory behavior even when measured time excludes scheduling.
    if(test_name STREQUAL "test_semantics_scaling")
        set_tests_properties("SOMTParser.${test_name}" PROPERTIES RUN_SERIAL TRUE)
    endif()
endforeach()

if(SOMTPARSER_TEST_TARGETS)
    add_custom_target(build_all_tests DEPENDS ${SOMTPARSER_TEST_TARGETS})
endif()

# docs/languages/*.md cite the tree by file and line, name HIR and Fidelity
# APIs, and cross-reference each other's sections. Every one of those is a claim
# that goes stale without anyone touching the document -- two in dimacs-cnf.md
# rotted the day after it was written, from an edit that inserted comment lines
# above the line they pointed at. Checked here so `ctest` covers it with
# everything else.
if(EXISTS "${PROJECT_SOURCE_DIR}/docs/languages")
    find_package(Python3 COMPONENTS Interpreter QUIET)
    if(Python3_Interpreter_FOUND)
        add_test(NAME SOMTParser.doc_citations
            COMMAND "${Python3_EXECUTABLE}"
                    "${PROJECT_SOURCE_DIR}/scripts/check-doc-citations.py")
        set_tests_properties(SOMTParser.doc_citations PROPERTIES
            WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}")
    else()
        # Said out loud rather than skipped in silence: a check that quietly
        # stops running is the failure mode this whole file exists to prevent.
        message(STATUS
            "No Python3 interpreter: SOMTParser.doc_citations will NOT run")
    endif()
endif()
