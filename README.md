# SOMTParser

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![PyPI](https://img.shields.io/pypi/v/somtparser.svg)](https://pypi.org/project/somtparser/)
[![Python](https://img.shields.io/pypi/pyversions/somtparser.svg)](https://pypi.org/project/somtparser/)

**SOMTParser** is a solver-independent C++17 front-end library for SMT-LIB and OMT (Optimization Modulo Theories). It parses input into a **typed DAG-based intermediate representation (IR)** and provides modular front-end functionality—parsing, type checking, traversals, rewriting, and formula-level processing—around this IR, separating reusable front-end logic from backend reasoning and reducing the effort to build new solvers and SMT-based tools.

## Design Overview

The native frontend parses SMT-LIB/OMT into the typed SMT expression DAG.
See [the source layout](docs/source-layout.md) for module responsibilities.

`main` contains the SMT parser and core maintenance. Future language frontends,
HIR, translation and natural-language modeling are maintained on
[`develop`](https://github.com/fuqi-jia/SOMTParser/tree/develop).

- **Frontend**: Command and term parsing, type checking, OMT-oriented input, and API-level expression construction feeding the same IR pipeline.
- **IR core**: A unified typed DAG representation with structure sharing and canonicalization via `NodeManager`; equal subterms are stored once.
- **Passes**: IR-based traversal (each node visited at most once) and rewriting (bottom-up, with fixpoint mode), plus a kind-based dispatch mechanism for extensions.
- **Utilities**: Formula conversion (NNF, CNF, DNF, including CDCL(T)-style Boolean abstraction), model parsing, and evaluation under full or partial models.

## Key Features

- **SMT-LIB2 support**: Parsing and typed representations for multiple SMT-LIB2 logics and theories.
- **FloatingPoint dialect**: By default the parser accepts small **lenient** extensions (e.g. unary `fp.sqrt` canonicalized to `(fp.sqrt RNE …)` in the IR, and aliases like `fp.=`). For **stricter** surface syntax aligned with the official FloatingPoint theory, enable `strict_smtlib_fp` (`Parser::setStrictSmtlib(true)` or `GlobalOptions::setOption("strict_smtlib_fp", "true")`).
- **Multi-theory**: Booleans, integer/real arithmetic, bitvectors, IEEE-754 floating point, strings and regular expressions, arrays.
- **Typed DAG IR**: Structure sharing and canonicalization for a more compact representation and easier analysis/transformation.
- **OMT support**: Parses intermediate syntax such as `assert-soft`, `maximize`/`minimize`, `define-objective`, `lex-optimize`/`pareto-optimize`/`box-optimize`, `maxsat`/`minsat`, managed by `ObjectiveManager`.
- **Programmatic construction**: Build terms and formulas via API, sharing the same IR as parsed input.
- **Formula conversion**: NNF, CNF, DNF; CNF supports theory-atom-to-Boolean abstraction and bidirectional mapping for CDCL(T)-style reasoning.
- **Model interface**: Parse solver-produced model output and evaluate formulas/terms under full or partial models.
- **Rewriting and traversal**: Extensible rewrite rules, kind-based dispatcher, visit-once traversal over the DAG.

## System Requirements

- C++17 compatible compiler
- CMake 3.16+
- GMP (GNU Multiple Precision Arithmetic Library)
- MPFR (GNU Multiple Precision Floating-Point Reliable Library)

### Installing Dependencies

#### Ubuntu/Debian
```bash
sudo apt update
sudo apt install -y \
  build-essential \
  g++ \
  cmake \
  libgmp-dev \
  libmpfr-dev
```

#### Fedora/RHEL/CentOS
```bash
# Fedora
sudo dnf install -y \
  gcc-c++ \
  cmake \
  gmp-devel \
  mpfr-devel

# RHEL/CentOS
sudo yum install -y \
  gcc-c++ \
  cmake \
  gmp-devel \
  mpfr-devel
```

#### macOS
Using [Homebrew](https://brew.sh/):
```bash
brew install \
  cmake \
  ninja \
  gmp \
  mpfr
```

#### Windows

##### Using MSYS2
1. Install [MSYS2](https://www.msys2.org/)
2. Open MSYS2 MinGW 64-bit terminal and run:
```bash
pacman -Syu
pacman -S \
  mingw-w64-x86_64-gcc \
  mingw-w64-x86_64-cmake \
  mingw-w64-x86_64-gmp \
  mingw-w64-x86_64-mpfr
```

##### Using vcpkg
1. Install [vcpkg](https://github.com/microsoft/vcpkg)
2. Install dependencies:
```bash
vcpkg install gmp:x64-windows mpfr:x64-windows
```

##### Using WSL (Windows Subsystem for Linux)
1. Install and set up [WSL](https://learn.microsoft.com/en-us/windows/wsl/install)
2. Follow the Ubuntu/Debian instructions to install dependencies within WSL

## Installation

### Standard CMake Build Process

```bash
# Clone the repository
git clone https://github.com/fuqi-jia/SOMTParser.git
cd SOMTParser

# Configure and build out of tree
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release
cmake --build build --parallel

# Install to a selected prefix
cmake --install build --prefix "$HOME/.local"
```

### Integration as Git Submodule

For projects using Git, SOMTParser can be included as a submodule:

```bash
# Add the repository as a submodule
git submodule add https://github.com/fuqi-jia/SOMTParser.git SOMTParser

# Initialize the submodule
git submodule update --init --recursive

# Update the submodule to the latest version when needed
git submodule update --remote --merge
```

### Build TEST

To build and run the tests:

```bash
cmake -S . -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Debug \
  -DSOMTPARSER_BUILD_TESTS=ON
cmake --build build --parallel
ctest --test-dir build --output-on-failure
```

You can also use the provided test script from the project root:

```bash
./test/run_all_tests.sh
```

### Build Configuration Options

| Option | Description | Default |
|--------|-------------|---------|
| `BUILD_SHARED_LIBS` | Build a shared rather than static library | OFF |
| `SOMTPARSER_BUILD_TESTS` | Build and register test executables with CTest | OFF |
| `BUILD_PYTHON` | Build the native SMT Python extension | OFF |
| `SOMTPARSER_WARNINGS_AS_ERRORS` | Treat warnings in SOMTParser sources as errors | OFF |
| `SOMTPARSER_ENABLE_TIMING` | Enable the timing profiler | OFF |

Third-party Homebrew headers are exposed through imported CMake targets and are not affected by `SOMTPARSER_WARNINGS_AS_ERRORS`.

### Compiling Client Applications

When building applications that use SOMTParser, link against the library and its dependencies:

```bash
g++ -std=c++17 -o application main.cpp -lsomtparser -lgmp -lmpfr
```

For CMake projects, you can use:

```cmake
# CMakeLists.txt
cmake_minimum_required(VERSION 3.10)
project(your_application)

set(CMAKE_CXX_STANDARD 17)

# Method 1: Using as Git submodule (recommended)
add_subdirectory(SOMTParser)

# Method 2: Use an installed package
# find_package(SOMTParser 1.0 CONFIG REQUIRED)

# Create your executable
add_executable(your_application main.cpp)

target_link_libraries(your_application PRIVATE SOMTParser::somtparser)
```

## Python Bindings

SOMTParser ships first-class Python bindings (pybind11) exposing the full
parsing, expression-building, transformation, model-evaluation and OMT API.

### Install

```bash
pip install somtparser
```

Prebuilt wheels are published on [PyPI](https://pypi.org/project/somtparser/) for
CPython 3.9–3.13 on Linux x86_64 (manylinux), macOS (Intel needs macOS 15+,
Apple Silicon needs macOS 14+) and Windows AMD64, with GMP/MPFR bundled — no
system dependencies required.

On any other platform `pip` falls back to building from the sdist, which needs
a C++17 compiler, CMake, GMP and MPFR (see
[System Requirements](#system-requirements)). The same applies when installing
from a checkout:

```bash
# from the repository root
pip install .
```

This builds a wheel via scikit-build-core with the static C++ core compiled in.

### Quick Start

```python
import somtparser as sp

# Parse SMT-LIB2 / OMT input
p = sp.parse("""
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> (+ x y) 0))
(minimize x)
""")
print(p.assertions[0].to_smt2())   # (> (+ x y) 0)
print(p.objectives[0].is_minimize) # True

# Build expressions programmatically
q = sp.Parser()
a, b = q.var_int("a"), q.var_int("b")
q.assert_(q.gt(q.add(a, b), q.const_int(0)))

# Evaluate under a solver model
m = p.parse_model("(model (define-fun x () Int 3) (define-fun y () Int 4))")
print(p.evaluate(p.assertions[0], m).value)  # True

# Normal forms
nnf = p.to_nnf(p.assertions[0])
top, clauses = p.to_tseitin_cnf(p.assertions)
```

### Feature Overview

- **Parsing**: `parse`, `parse_file`, incremental `parse_string`, `push`/`pop`,
  strict-mode and option control; parse errors raise `somtparser.ParseError`.
- **Expression building**: all SMT-LIB theories — Bool, Int/Real (incl.
  transcendental functions), BitVec, FloatingPoint, String/RegLan, Array,
  quantifiers, uninterpreted/defined functions. Invalid constructions raise
  `ValueError` / `TypeError` instead of returning broken nodes.
- **Transformations**: `substitute`, `replace_nodes`, `expand_let`,
  `negate_comp`/`converse_comp`/`mirror_comp`, `binarize_op`,
  `collect_vars`/`collect_atoms`,
  NNF / CNF / DNF / Tseitin CNF with atom-abstraction maps.
- **Models & evaluation**: dict-like `Model`, `parse_model` for solver output,
  exact big-integer/rational values (`Fraction`), partial-model evaluation.
- **OMT**: `minimize`/`maximize`/`define-objective`/`lex-optimize`/
  `pareto-optimize`/`box-optimize`/`maxsat`, soft assertions with weights and
  groups, exposed via `parser.objectives`.
- **Safety**: nodes stay valid after their `Parser` is garbage-collected;
  arbitrary-precision Python ints map to GMP exactly; type stubs
  (`py.typed`, `.pyi`) included.

### Running the Python Tests

```bash
pip install pytest
pytest test/python -q
```

## Configuration Options

SOMTParser provides various configuration options through the `GlobalOptions` class to control parsing behavior, evaluation settings, and other aspects.

### Quick Start

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    auto parser = SOMTParser::newParser();

    // Set options via direct methods
    parser->getOptions()->setLogic("QF_LIA");
    parser->getOptions()->setKeepLet(false);
    parser->getOptions()->setEvaluatePrecision(256);
    parser->getOptions()->preserveOperators({
        SOMTParser::NT_STR_REPLACE,
        SOMTParser::NT_STR_REPLACE_ALL
    });

    // Or via string interface
    parser->getOptions()->setOption("keep_let", "false");
    parser->getOptions()->setOption("precision", "256");

    // Print detailed configuration report
    std::cout << parser->optionToString() << std::endl;
    return 0;
}
```

### Available Options

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| **logic** | string | `UNKNOWN_LOGIC` | SMT-LIB2 logic (e.g., `QF_LIA`, `QF_BV`, `ALL`) |
| **precision** | uint | `128` | MPFR floating-point precision in bits |
| **float_evaluate** | bool | `true` | Use floating-point (true) or exact rational (false) arithmetic |
| **keep_division** | bool | `true` | Preserve division if not exact (e.g., `(/ 5 2)` stays as-is) |
| **keep_let** | bool | `true` | Preserve let-bindings instead of expanding inline |
| **expand_functions** | bool | `false` | When true, inline function calls with definitions; when false (default), preserve as function applications |
| **preserved_operators** | set of `NODE_KIND` | empty | Keep selected operators explicit in the DAG even when their arguments are ground; configure with `preserveOperator(s)` rather than the string option interface |
| **Command Flags** | bool | `false` | Tracks encountered SMT-LIB2 commands: `check_sat`, `get_model`, `get_assertions`, `get_proof`, `get_unsat_core`, `get_objectives`, etc. |

<!-- 
**Planned Feature:**
| **expand_recursive_functions** | bool | `false` | Expand `define-fun-rec` like regular functions |
This feature is planned for future implementation. It will use a 'this' placeholder mechanism to handle 
recursive self-references during function body parsing and expansion. Currently, recursive functions 
are preserved as-is in their original form.
-->

### Setting Options

```cpp
#include "somtparser/parser.h"

int main() {
    auto parser = SOMTParser::newParser();

    // Method 1: Direct setters (recommended)
    parser->getOptions()->setLogic("QF_LIA");
    parser->getOptions()->setEvaluatePrecision(256);
    parser->getOptions()->setKeepLet(false);
    parser->getOptions()->setExpandFunctions(false);  // Preserve function applications

    // Method 2: String interface (useful for SMT-LIB2 compatibility)
    parser->setOption("precision", "256");
    parser->setOption("keep_let", "false");
    parser->setOption("expand_functions", "false");

    return 0;
}
```

### Configuration Report

The `toString()` method generates a comprehensive report with all settings, defaults, and descriptions:

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    auto parser = SOMTParser::newParser();
    std::cout << parser->optionToString() << std::endl;
    return 0;
}
```

## API Reference

### Core Components and Smart Pointer Types

| Component | Smart Pointer Type | Description |
|-----------|-------------------|-----------|
| `Parser` | `ParserPtr` | Main class for parsing SMT-LIB2 files and managing expressions |
| `DAGNode` | `NodePtr` | Represents expressions as nodes in a "directed acyclic graph" |
| `Sort` | `SortPtr` | Encapsulates SMT-LIB2 type system |
| `Objective` | `ObjectivePtr` | Represents optimization objectives for OMT problems |
| `SingleObjective` | `SingleObjectivePtr` | Represents a single optimization objective |
| `MetaObjective` | `MetaObjectivePtr` | Represents a meta-optimization objective |
| `Model` | `ModelPtr` | Represents a model with variable assignments |

### Factory Methods

| Method | Description |
|--------|-----------|
| `newParser()` | Creates a new parser instance |
| `newParser(const std::string& filename)` | Creates a new parser and parses the specified file |
| `newModel()` | Creates a new model instance |

### Primary API Functions

| Category | Function Examples |
|----------|------------------|
| **Variable Creation** | `mkVar`, `mkVarInt`, `mkVarReal`, `mkVarBool`, `mkTempVar`, ... |
| **Constant Creation** | `mkConstInt`, `mkConstReal`, `mkTrue`, `mkFalse`, `mkConstStr`, ... |
| **Expression Building** | `mkOper`, `mkEq`, `mkDistinct`, `mkNot`, `mkAnd`, `mkOr`, `mkIte`, ... |
| **Arithmetic Operations** | `mkAdd`, `mkSub`, `mkMul`, `mkDiv`, `mkPow`, `mkAbs`, `mkMod`, ... |
| **Comparison Operations** | `mkLt`, `mkLe`, `mkGt`, `mkGe`, ... |
| **Bitvector Operations** | `mkBvAnd`, `mkBvOr`, `mkBvXor`, `mkBvAdd`, `mkBvShl`, `mkBvLshr`, ... |
| **String Operations** | `mkStrLen`, `mkStrConcat`, `mkStrSubstr`, `mkStrIndexof`, ... |
| **Regular Expression Operations** | `mkStrToReg`, `mkRegUnion`, `mkRegStar`, `mkRegInter`, ... |
| **Array Operations** | `mkSelect`, `mkStore`, ... |
| **Floating Point Operations** | `mkFpAdd`, `mkFpMul`, `mkFpDiv`, `mkFpEq`, `mkFpLt`, ... |
| **Formula Evaluation** | `evaluate`, `setEvaluatePrecision`, `setEvaluateUseFloating`, ... |
| **Format Conversion** | `toCNF`, `toDNF`, `toNNF`, `toTseitinCNF`, ... |
| **Formula Analysis** | `collectAtoms`, `collectVars`, `expandLet`, `replaceAtoms`, ... |
| **Model Operations** | `add`, `get`, `isEmpty`, `toString`, ... |
| **Incremental / Command** | `push`, `pop`, `resetAssertions`, `reset`, `nextCommand`, `getScript`, `setCommandLogging` |
| **Debugging & Output** | `toString`, `getAssertions`, ... |

## Usage Examples

All public APIs (parser, passes, visitor, rewriter, op-dispatcher, etc.) are exposed through a single **umbrella header**. Include it once; no need to include individual component headers.

```cpp
#include "somtparser/parser.h"
using namespace SOMTParser;
// Parser parser; ...
```

The examples below assume this include (and optionally `using namespace SOMTParser`).

### Basic Parsing and Expression Building

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    // Initialize the parser
    SOMTParser::Parser parser;

    // Parse an SMT-LIB2 file
    if (!parser.parse("formula.smt2")) {
        std::cerr << "Error parsing file" << std::endl;
        return 1;
    }

    // Retrieve the parsed assertions
    auto assertions = parser.getAssertions();

    // Output the assertions
    for(auto constraint: assertions){
        std::cout << parser.toString(constraint) << std::endl;
    }

    return 0;
}
```

### Expression Building

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    auto parser = SOMTParser::newParser();
    
    // Create variables and expressions
    auto x = parser->mkVarInt("x");
    auto y = parser->mkVarInt("y");
    auto sum = parser->mkAdd(std::vector<std::shared_ptr<SOMTParser::DAGNode>>{x, y});
    auto condition = parser->mkGt(sum, parser->mkConstInt(10));
    
    std::cout << "Sum expression: " << parser->toString(sum) << std::endl;
    std::cout << "Condition: " << parser->toString(condition) << std::endl;
    
    return 0;
}
```





## Some Useful Features

### Formula Analysis

Analysis and manipulation of formulas:

```cpp
#include "somtparser/parser.h"
#include <iostream>
#include <unordered_set>

int main() {
    auto parser = SOMTParser::newParser();
    
    // Create variables and build complex formula
    auto x = parser->mkVarInt("x");
    auto y = parser->mkVarInt("y");
    auto z = parser->mkVarBool("z");
    
    std::vector<std::shared_ptr<SOMTParser::DAGNode>> parts = {
        parser->mkGt(parser->mkAdd(std::vector<std::shared_ptr<SOMTParser::DAGNode>>{x, y}), parser->mkConstInt(0)),
        parser->mkLt(x, parser->mkConstInt(10)),
        z
    };
    auto formula = parser->mkAnd(parts);
    
    // Collect atoms and variables
    std::unordered_set<std::shared_ptr<SOMTParser::DAGNode>> atoms, vars;
    parser->collectAtoms(formula, atoms);
    parser->collectVars(formula, vars);
    
    std::cout << "Formula: " << parser->toString(formula) << std::endl;
    // Output: (and (< x 10) (> (+ y x) 0) z)
    
    std::cout << "Found " << atoms.size() << " atoms and " << vars.size() << " variables" << std::endl;
    // Output: Found 2 atoms and 3 variables
    
    return 0;
}
```

### Formula Format Conversions

Convert formulas between different normal forms:

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    auto parser = SOMTParser::newParser();
    auto a = parser->mkVarBool("a");
    auto b = parser->mkVarBool("b");
    auto c = parser->mkVarBool("c");

    // Build complex formula
    auto formula = parser->mkAnd(std::vector<std::shared_ptr<SOMTParser::DAGNode>>{
        parser->mkImplies(a, b),
        parser->mkOr(std::vector<std::shared_ptr<SOMTParser::DAGNode>>{b, c})
    });

    // Convert to different normal forms
    auto nnf = parser->toNNF(formula);
    auto cnf = parser->toCNF(std::vector<std::shared_ptr<SOMTParser::DAGNode>>{formula});
    auto dnf = parser->toDNF(formula);

    std::cout << "Original: " << parser->toString(formula) << std::endl;
    std::cout << "NNF: " << parser->toString(nnf) << std::endl;
    std::cout << "CNF: " << parser->toString(cnf) << std::endl;
    std::cout << "DNF: " << parser->toString(dnf) << std::endl;
    return 0;
}
```

### CNF and Boolean abstraction

The CNF conversion can associate theory atoms with fresh Boolean variables and maintain the mapping in both directions (useful for CDCL(T)-style reasoning). After building CNF, you can get the abstraction variable for an atom and recover the atom from a CNF Boolean variable:

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    SOMTParser::Parser parser;
    parser.parseStr("(declare-const x Int)");
    parser.parseStr("(declare-const y Int)");

    SOMTParser::Node phi = parser.mkExpr("(and (> x 0) (< y 3))");
    SOMTParser::Node nnf = parser.toNNF(phi);
    SOMTParser::Node cnf = parser.toCNF({phi});  // vector of assertions

    SOMTParser::Node b = parser.getCNFBoolVar(parser.mkExpr("(> x 0)"));
    SOMTParser::Node a = parser.getCNFAtom(b);   // recovers (> x 0)

    std::cout << "Atom from CNF bool var: " << parser.toString(a) << std::endl;
    return 0;
}
```

### Model Evaluation

Evaluate logical formulas with mathematical functions and variable assignments:

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    auto parser = SOMTParser::newParser();
    auto model = SOMTParser::newModel();

    // Create a formula: (sin(x) > 0) ∧ (y > 1) ∧ (z ⟹ (x + y > 3))
    auto x = parser->mkVarReal("x");
    auto y = parser->mkVarReal("y");
    auto z = parser->mkVarBool("z");

    auto sin_x = parser->mkSin(x);
    auto cond1 = parser->mkGt(sin_x, parser->mkConstReal(std::string("0")));
    auto cond2 = parser->mkGt(y, parser->mkConstReal(std::string("1")));
    auto sum_xy = parser->mkAdd(std::vector<std::shared_ptr<SOMTParser::DAGNode>>{x, y});
    auto cond3 = parser->mkImplies(z, parser->mkGt(sum_xy, parser->mkConstReal(std::string("3"))));
    auto formula = parser->mkAnd(std::vector<std::shared_ptr<SOMTParser::DAGNode>>{cond1, cond2, cond3});

    // Assign values and evaluate
    model->add(x, parser->mkConstReal(std::string("1.5")));
    model->add(y, parser->mkConstReal(std::string("2.0")));
    model->add(z, parser->mkTrue());

    auto result = parser->evaluate(formula, model);
    std::cout << "Formula: " << parser->toString(formula) << std::endl;
    std::cout << "Result: " << parser->toString(result) << std::endl;
    return 0;
}
```

You can also parse solver-produced model output and then evaluate a formula under that model:

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    SOMTParser::Parser parser;
    parser.parseStr("(declare-const x Int)");
    parser.parseStr("(declare-const y Int)");
    SOMTParser::Node phi = parser.mkExpr("(and (> x 0) (> y 0))");

    std::string modelStr = R"(
(model
  (define-fun x () Int 1)
  (define-fun y () Int 2)
))";

    auto M = parser.parseModel(modelStr);
    SOMTParser::Node psi = parser.evaluate(phi, M);
    std::cout << "Evaluated: " << parser.toString(psi) << std::endl;
    return 0;
}
```

### Let Expression Expansion

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    auto parser = SOMTParser::newParser();
    auto x = parser->mkVarInt("x");
    auto y = parser->mkVarInt("y");
    auto let_expr = parser->mkExpr("(let ((temp (+ x 1))) (> temp y))");
    auto expanded = parser->expandLet(let_expr);

    std::cout << "Let expression: " << parser->toString(let_expr) << std::endl;
    std::cout << "Expanded: " << parser->toString(expanded) << std::endl;
    return 0;
}
```

### Optimization Modulo Theories (OMT)

```cpp
#include "somtparser/parser.h"
#include <iostream>

int main() {
    auto parser = SOMTParser::newParser();

    parser->parseStr("(declare-const x Int)");
    parser->parseStr("(declare-const y Int)");
    parser->parseStr("(assert (> x 0))");
    parser->parseStr("(assert (> y 0))");
    parser->parseStr("(assert-soft (< x 100) :weight 1.0)");
    parser->parseStr("(assert-soft (< y 50) :weight 2.0)");

    auto soft_assertions = parser->getSoftAssertions();
    auto soft_weights = parser->getSoftWeights();

    std::cout << "Found " << soft_assertions.size() << " soft assertions" << std::endl;
    for (size_t i = 0; i < soft_assertions.size(); ++i) {
        std::cout << "Soft assertion " << i << " (weight " << soft_weights[i] << "): "
                  << parser->toString(soft_assertions[i]) << std::endl;
    }
    return 0;
}
```

### DAG traversal (visit-once)

Because the IR is a DAG, the same subterm may appear in many places. The traversal API visits each distinct node at most once. For example, for `(and (or a b) (or a b))` the shared subterm `(or a b)` is visited once, so the walk sees exactly 4 nodes:

```cpp
#include "somtparser/parser.h"
#include <iostream>
#include <map>

using namespace SOMTParser;

class KindCounter : public NodeVisitor {
public:
    void visit(Node n) override { counts[kind(n)]++; }
    std::map<NODE_KIND, size_t> counts;
};

int main() {
    Parser parser;
    parser.parseStr("(declare-const a Bool)");
    parser.parseStr("(declare-const b Bool)");
    Node phi = parser.mkExpr("(and (or a b) (or a b))");

    KindCounter c;
    c.walk(phi);
    std::cout << "Total nodes (visit-once): " << c.counts.size() << " kinds" << std::endl;
    return 0;
}
```

### Rewriting

The rewriter performs bottom-up transformations; you can install default rules and run fixpoint rewriting so that a formula like `(and true (not (not p)))` simplifies to `p`:

```cpp
#include "somtparser/parser.h"
#include <iostream>

using namespace SOMTParser;

int main() {
    Parser parser;
    parser.parseStr("(declare-const p Bool)");
    parser.parseStr("(assert (and true (not (not p))))");

    Rewriter rw(parser.getNodeManager());
    installDefaultRewriteRules(rw);

    Node result = rw.rewrite(parser.getAssertions().back());
    std::cout << "Rewritten to: " << parser.toString(result) << std::endl;
    return 0;
}
```

### Kind-based dispatch (term depth)

Analysis or transformation logic can be organized by node kind using `OpDispatcher`: register handlers per kind and use `otherwise` for the default recursive behavior. Below, a small context holds the dispatcher so handlers can recurse to compute term depth:

```cpp
#include "somtparser/parser.h"
#include <iostream>

using namespace SOMTParser;

struct DepthContext : Context {
    OpDispatcher<int, Context>* disp = nullptr;
};

static int depthDefault(Node n, Context& ctx) {
    auto& dc = static_cast<DepthContext&>(ctx);
    int d = 0;
    for (Node c : children(n))
        if (c) d = std::max(d, dc.disp->dispatch(c, ctx));
    return 1 + d;
}

int main() {
    Parser parser;
    parser.parseStr("(declare-const x Int)");
    parser.parseStr("(assert (and (> x 0) (< x 10)))");
    Node root = parser.getAssertions().back();

    OpDispatcher<int, Context> disp;
    disp.onAND(depthDefault).onGT(depthDefault).onLT(depthDefault).otherwise(depthDefault);
    DepthContext dctx;
    dctx.disp = &disp;
    int depth = disp.dispatch(root, dctx);
    std::cout << "Term depth: " << depth << std::endl;
    return 0;
}
```

### Key Performance and Implementation Notes

- **DAG and canonicalization**: `NodeManager` interns nodes at construction time; structurally equal subterms are shared for a more compact IR.
- **Partial model evaluation**: Evaluate formulas/terms under partial models; under-specified subterms can be simplified.
- **Tseitin CNF**: Formula conversion suited for integration with SAT/CDCL(T)-style reasoning.
- **High-precision arithmetic**: Configurable MPFR precision.
- **Rewriting**: Single-round and fixpoint modes; rewritten results are rebuilt via `NodeManager` to preserve canonicalization.

## API Documentation

You can generate detailed API documentation using Doxygen:

### Installing Doxygen

#### Ubuntu/Debian
```bash
sudo apt-get install doxygen
```

#### CentOS/RHEL
```bash
sudo yum install doxygen
```

#### macOS
```bash
brew install doxygen
```

### Generating Documentation

To generate the documentation, run:

```bash
cd path/to/SOMTParser
doxygen Doxyfile
```

### Viewing Documentation

After generating the documentation, you can view it in your browser:

```bash
# Linux
xdg-open docs/html/index.html

# macOS
open docs/html/index.html

# Windows
start docs/html/index.html
```

Or simply navigate to `SOMTParser/docs/html/index.html` in your file browser and open it with any web browser.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Contributing

We welcome contributions from the community! Please see our [CONTRIBUTORS.md](CONTRIBUTORS.md) file for detailed information on how to contribute to this project.

## Development Status

**Active Development** — The project is under continuous maintenance and development; new features and optimizations are added regularly.

## Contact

For technical inquiries or support, please contact:

**Fuqi Jia**  
Email: jiafq@ios.ac.cn  
Institute of Software, Chinese Academy of Sciences


### Native recursive definitions and heap syntax

Recursive calls retain an immutable declaration node as child zero, followed by
actual arguments. `Parser::getRecursiveDefinitions()` returns `{symbol,
definition}` entries for the active scope; definitions expose their body and
formal parameters through `getFuncBody()` and `getFuncParams()`. Match calls to
this environment by symbol identity. Keep a copy of the environment when retaining
an assertion snapshot across `pop` or `reset`. Definition bodies never own a back
edge to another definition, so recursive and mutually recursive inputs remain
acyclic DAGs. Function substitution matches formal parameter identity and leaves
inner quantifier binders intact.

The parser accepts `declare-heap`, `sep.emp`, `pto`, `sep`, `wand`, and qualified
`(as sep.nil Sort)`. It checks heap signatures and preserves spatial operators in
the native DAG; heap satisfiability and inductive semantics belong to the consuming
solver. `getHeapLocationSort()` and `getHeapDataSort()` expose the active signature.

CMake clients that only need native DAGs and exact numeric values can link
`SOMTParser::somtparser_ir`. Its object files are shared with the full parser build.
