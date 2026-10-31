/* -*- Source -*-
 * Explicit language registration.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/register_all.h"
#include "somtparser/languages/minizinc.h"
#include "somtparser/languages/qcir.h"
#include "somtparser/languages/qdimacs.h"
#include "somtparser/languages/dimacs.h"
#include "somtparser/languages/wcnf.h"
#include "somtparser/languages/opb.h"
#include "somtparser/languages/lp.h"
#include "somtparser/languages/mps.h"
#include "somtparser/languages/flatzinc.h"
#include "somtparser/languages/tptp.h"
#include "somtparser/languages/xcsp3.h"
#include "somtparser/languages/cryptoline.h"
#include "somtparser/languages/chc.h"
#include "somtparser/languages/smtlib2.h"
#include "somtparser/languages/boogie.h"
#include "somtparser/languages/essence.h"
#include "somtparser/languages/btor2.h"
#include "somtparser/languages/aiger.h"
#include "somtparser/languages/vmt.h"
#include "somtparser/languages/moxi.h"
#include "somtparser/languages/sygus.h"
#include "somtparser/languages/syntcomp.h"
#include "somtparser/languages/pddl.h"
#include "somtparser/languages/hddl.h"

namespace SOMTParser::Lang {

void registerAllLanguages(LanguageRegistry& registry) {
    if (registry.byId("hddl") == nullptr) {
        registry.add(mkHddlLanguage());
    }
    if (registry.byId("pddl") == nullptr) {
        registry.add(mkPddlLanguage());
    }
    if (registry.byId("sygus") == nullptr) {
        registry.add(mkSygusLanguage());
    }
    if (registry.byId("syntcomp") == nullptr) {
        registry.add(mkSyntcompLanguage());
    }
    if (registry.byId("moxi") == nullptr) {
        registry.add(mkMoxiLanguage());
    }
    if (registry.byId("vmt") == nullptr) {
        registry.add(mkVmtLanguage());
    }
    if (registry.byId("aiger") == nullptr) {
        registry.add(mkAigerLanguage());
    }
    if (registry.byId("btor2") == nullptr) {
        registry.add(mkBtor2Language());
    }
    if (registry.byId("essence") == nullptr) {
        registry.add(mkEssenceLanguage());
    }
    if (registry.byId("boogie") == nullptr) {
        registry.add(mkBoogieLanguage());
    }
    if (registry.byId("smtlib2") == nullptr) {
        registry.add(mkSmtLib2Language());
    }
    if (registry.byId("chc") == nullptr) {
        registry.add(mkChcLanguage());
    }
    if (registry.byId("minizinc") == nullptr) {
        registry.add(mkMiniZincLanguage());
    }
    if (registry.byId("qcir") == nullptr) {
        registry.add(mkQcirLanguage());
    }
    if (registry.byId("qdimacs") == nullptr) {
        registry.add(mkQdimacsLanguage());
    }
    if (registry.byId("dimacs") == nullptr) {
        registry.add(mkDimacsLanguage());
    }
    if (registry.byId("wcnf") == nullptr) {
        registry.add(mkWcnfLanguage());
    }
    if (registry.byId("opb") == nullptr) {
        registry.add(mkOpbLanguage());
    }
    if (registry.byId("lp") == nullptr) {
        registry.add(mkLpLanguage());
    }
    if (registry.byId("mps") == nullptr) {
        registry.add(mkMpsLanguage());
    }
    if (registry.byId("flatzinc") == nullptr) {
        registry.add(mkFlatZincLanguage());
    }
    if (registry.byId("tptp") == nullptr) {
        registry.add(mkTptpLanguage());
    }
    if (registry.byId("xcsp3") == nullptr) {
        registry.add(mkXcsp3Language());
    }
    if (registry.byId("cryptoline") == nullptr) {
        registry.add(mkCryptoLineLanguage());
    }
}

} // namespace SOMTParser::Lang
