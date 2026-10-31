"""Portable controls for provider constraint-name annotations."""
from copy import deepcopy
from somtparser.hir import build_hir
from somtparser.hir_provider_forms import adapt_provider_forms

def model(constraint):
    return {"schema":"somt-hir-model-v1","language":"hir","decision":"satisfiability",
            "declarations":[],"functions":[],"constraints":[constraint],"objectives":[],
            "assumptions":[],"unresolved":[],"goal":None,"objective_order":"single"}

def test_string_name_is_removed_only_from_exact_constraint_shape_and_ledger_replays():
    source="true."
    raw=model({"name":"label","expr":{"literal":True,"sort":"Bool"},"span":[0,len(source)]})
    before=deepcopy(raw)
    adapted,ledger=adapt_provider_forms(raw)
    assert raw==before
    assert adapted["constraints"][0]=={"expr":{"literal":True,"sort":"Bool"},"span":[0,len(source)]}
    assert len(ledger)==1 and ledger[0]["before"]["name"]=="label"
    replay=deepcopy(raw)
    for entry in ledger:
        assert replay["constraints"][0]==entry["before"]
        replay["constraints"][0]=deepcopy(entry["after"])
    assert replay==adapted
    assert adapt_provider_forms(adapted)==(adapted,[])
    assert build_hir(adapted,source).translate().ok

def test_nonstring_names_and_other_unknown_fields_remain_unmodified():
    base={"expr":{"literal":True,"sort":"Bool"},"span":[0,5]}
    for extra in ({"name":7},{"name":"tag","note":"unknown"}):
        raw=model(dict(base,**extra))
        assert adapt_provider_forms(raw)==(raw,[])
