# The public-corpus PDDL driver uses the project's core and language libraries.
add_executable(pddl_translate pddl_translate.cpp)
target_compile_features(pddl_translate PRIVATE cxx_std_17)
target_link_libraries(pddl_translate PRIVATE SOMTParser::languages)
install(TARGETS pddl_translate RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})

# Optional helpers for semantic regression tests; these are not installed CLIs.
if(SOMTPARSER_BUILD_TESTS)
    # Independent exact certificate; does not link the frontend or HIR implementation.
    add_executable(somt-wcnf-certificate semantic_checks/wcnf_exact_certificate.cpp)
    target_compile_features(somt-wcnf-certificate PRIVATE cxx_std_17)

    # Whole-module parser bridge; exact source/cost checking is a separate tool.
    add_executable(somt-wcnf-load-bridge semantic_checks/wcnf_load_bridge.cpp)
    target_compile_features(somt-wcnf-load-bridge PRIVATE cxx_std_17)
endif()
