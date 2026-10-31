/* -*- Source -*-
 * Command and Script implementation
 */

#include "somtparser/frontend/command.h"
#include "somtparser/frontend/parser.h"

namespace SOMTParser {

const char* commandTypeName(CMD_TYPE type) noexcept {
    switch (type) {
    case CMD_TYPE::CT_UNKNOWN: return "unknown";
    case CMD_TYPE::CT_EOF: return "eof";
    case CMD_TYPE::CT_ASSERT: return "assert";
    case CMD_TYPE::CT_CHECK_SAT: return "check-sat";
    case CMD_TYPE::CT_CHECK_SAT_ASSUMING: return "check-sat-assuming";
    case CMD_TYPE::CT_DECLARE_CONST: return "declare-const";
    case CMD_TYPE::CT_DECLARE_FUN: return "declare-fun";
    case CMD_TYPE::CT_DECLARE_SORT: return "declare-sort";
    case CMD_TYPE::CT_DECLARE_DATATYPES: return "declare-datatypes";
    case CMD_TYPE::CT_DECLARE_HEAP: return "declare-heap";
    case CMD_TYPE::CT_DECLARE_CODATATYPES: return "declare-codatatypes";
    case CMD_TYPE::CT_DEFINE_FUN: return "define-fun";
    case CMD_TYPE::CT_DEFINE_FUN_REC: return "define-fun-rec";
    case CMD_TYPE::CT_DEFINE_FUNS_REC: return "define-funs-rec";
    case CMD_TYPE::CT_DEFINE_SORT: return "define-sort";
    case CMD_TYPE::CT_ECHO: return "echo";
    case CMD_TYPE::CT_EXIT: return "exit";
    case CMD_TYPE::CT_GET_ASSERTIONS: return "get-assertions";
    case CMD_TYPE::CT_GET_ASSIGNMENT: return "get-assignment";
    case CMD_TYPE::CT_GET_INFO: return "get-info";
    case CMD_TYPE::CT_GET_MODEL: return "get-model";
    case CMD_TYPE::CT_GET_OPTION: return "get-option";
    case CMD_TYPE::CT_GET_PROOF: return "get-proof";
    case CMD_TYPE::CT_GET_UNSAT_ASSUMPTIONS: return "get-unsat-assumptions";
    case CMD_TYPE::CT_GET_UNSAT_CORE: return "get-unsat-core";
    case CMD_TYPE::CT_GET_VALUE: return "get-value";
    case CMD_TYPE::CT_POP: return "pop";
    case CMD_TYPE::CT_PUSH: return "push";
    case CMD_TYPE::CT_RESET: return "reset";
    case CMD_TYPE::CT_RESET_ASSERTIONS: return "reset-assertions";
    case CMD_TYPE::CT_SET_INFO: return "set-info";
    case CMD_TYPE::CT_SET_LOGIC: return "set-logic";
    case CMD_TYPE::CT_SET_OPTION: return "set-option";
    case CMD_TYPE::CT_EXISTS: return "exists";
    case CMD_TYPE::CT_FORALL: return "forall";
    case CMD_TYPE::CT_GET_OBJECTIVES: return "get-objectives";
    case CMD_TYPE::CT_ASSERT_SOFT: return "assert-soft";
    case CMD_TYPE::CT_DEFINE_OBJ: return "define-objective";
    case CMD_TYPE::CT_DEFINE_MIN_OBJ: return "define-min-objective";
    case CMD_TYPE::CT_DEFINE_MAX_OBJ: return "define-max-objective";
    case CMD_TYPE::CT_MINIMIZE: return "minimize";
    case CMD_TYPE::CT_MAXIMIZE: return "maximize";
    case CMD_TYPE::CT_LEX_OPTIMIZE: return "lex-optimize";
    case CMD_TYPE::CT_PARETO_OPTIMIZE: return "pareto-optimize";
    case CMD_TYPE::CT_BOX_OPTIMIZE: return "box-optimize";
    case CMD_TYPE::CT_MINMAX: return "minmax";
    case CMD_TYPE::CT_MAXMIN: return "maxmin";
    case CMD_TYPE::CT_MAXSAT: return "maxsat";
    case CMD_TYPE::CT_MINSAT: return "minsat";
    case CMD_TYPE::CT_OPTIMIZE: return "optimize";
    }
    return "unknown";
}

bool Command::isAssert() const { return type == CMD_TYPE::CT_ASSERT; }
bool Command::isPush() const { return type == CMD_TYPE::CT_PUSH; }
bool Command::isPop() const { return type == CMD_TYPE::CT_POP; }
bool Command::isReset() const { return type == CMD_TYPE::CT_RESET; }
bool Command::isResetAssertions() const { return type == CMD_TYPE::CT_RESET_ASSERTIONS; }
bool Command::isCheckSat() const { return type == CMD_TYPE::CT_CHECK_SAT; }
bool Command::isCheckSatAssuming() const { return type == CMD_TYPE::CT_CHECK_SAT_ASSUMING; }
const char* Command::kindName() const noexcept { return commandTypeName(type); }

void Script::addCommand(const Command& cmd) {
    commands_.push_back(cmd);
}

void Script::addCommand(Command&& cmd) {
    commands_.push_back(std::move(cmd));
}

const std::vector<Command>& Script::commands() const {
    return commands_;
}

size_t Script::size() const {
    return commands_.size();
}

const Command& Script::operator[](size_t i) const {
    return commands_[i];
}

void Script::clear() {
    commands_.clear();
}

} // namespace SOMTParser
