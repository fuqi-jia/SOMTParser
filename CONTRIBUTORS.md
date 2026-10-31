# Contributors

This document recognizes the people who have contributed to the SOMTParser project.

## Project Creator & Lead Maintainer

**Fuqi Jia** - *Creator and Lead Developer*
- Email: jiafq@ios.ac.cn
- Affiliation: Institute of Software, Chinese Academy of Sciences
- Contributions: Project architecture, core parser implementation, all major features

## How to Contribute

We welcome contributions from the community! Here are some ways you can help:

### Code Contributions
- Bug fixes
- Feature improvements
- Performance optimizations
- Documentation improvements
- Test case additions

### Other Contributions
- Reporting bugs and issues
- Suggesting new features
- Improving documentation
- Code reviews
- Testing and validation

## Contribution Guidelines

SMT parser and core SMT fixes, including compiler/build compatibility, go
directly to `main`. Future technical work, including language translation,
new language frontends and related HIR/lowering extensions, belongs on
`develop`. Shared SMT fixes can be ported from `main` to `develop` as needed;
promotion of future features into `main` is a separate integration.

1. **Fork the repository** and create a feature branch from the appropriate target branch above
2. **Follow the coding style** used in the existing codebase
3. **Add tests** for any new functionality
4. **Update documentation** if needed
5. **Ensure all tests pass** by running `./test/run_all_tests.sh`
6. **Submit a pull request** against that target branch with a clear description of your changes

## Recognition

All contributors will be recognized in this file. When you make your first contribution, please add your name to the list below:

### Contributors

**Rui Han** - *Floating-point declarations and definitions support, string bug fixes*
- Implemented floating-point variable declarations and definitions
- Fixed various string-related bugs and issues

**Kunhang Lv** - *String output functionality improvements*
- Enhanced string conversion and output mechanisms

**Cunjing Ge & Minghao Liu** - Initial prototype developers (~2k lines)

<!-- Add your name here when you make your first contribution -->
<!-- Format: **Your Name** - *Brief description of contribution* -->
<!-- Example: **John Doe** - *Bug fixes in expression parser* -->

## Acknowledgements

These are not project contributors, but their published work fed back into
SOMTParser and deserves credit.

- **SMTStabilizer** (<https://github.com/shaowei-cai-group/SMTStabilizer>, MIT,
  © 2026 Xiang Zhang) vendors and extends SOMTParser's parser. Reviewing that
  fork surfaced several printer bugs on our side (the `bv2int`/`int2bv`
  conversions printing as `UNKNOWN_KIND`, the regex sort printing as
  `(RegEx String)` instead of `RegLan`, and the datatype tester printing in the
  legacy `(is-C x)` form), and its implementations of the tuple theory,
  `((_ update <selector>) t v)`, the SMT-LIB 2.7 `ubv_to_int`/`sbv_to_int`
  spellings and term-annotation preservation were used as the reference when
  adding those features here. The individual call sites carry inline notes.

---

## Contact

For questions about contributing, please contact:
- **Fuqi Jia**: jiafq@ios.ac.cn

Thank you to everyone who has contributed to making SOMTParser better!
