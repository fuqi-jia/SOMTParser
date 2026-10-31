"""Comparison-side metadata for source-bound explicit coordinate maps.

This helper does not infer a map. Callers must derive the coordinate list from
the source and instance, then provide the corresponding explicit map entries.
For partially exported arrays it annotates only a copied metadata object so
the finite-observable checker knows which reference cells are actually public.
"""

from copy import deepcopy


class CoordinateMetadataError(ValueError):
    pass


def _shape(value, name):
    if not isinstance(value, (list, tuple)) or any(
            type(size) is not int or size <= 0 for size in value):
        raise CoordinateMetadataError(f"{name} shape must contain positive exact integers")
    return tuple(value)


def _index(value, shape, name):
    if not isinstance(value, (list, tuple)) or any(type(part) is not int for part in value):
        raise CoordinateMetadataError(f"{name} must be an integer coordinate")
    coord = tuple(value)
    if len(coord) != len(shape) or any(part < 0 or part >= bound
                                        for part, bound in zip(coord, shape)):
        raise CoordinateMetadataError(f"{name} {coord} is outside shape {shape}")
    return coord


def comparison_metadata_for_explicit_maps(reference_metadata, coordinate_maps,
                                         source_observed_indices):
    """Return a validated comparison-only copy with sparse cells explicit.

    Each map must have ``reference_name`` and a ``coordinates`` list containing
    ``reference_index`` entries. The list must cover exactly the exported
    ``elements`` for that reference observable, with no duplicates. A partial
    shape is marked sparse and receives ``observed_indices`` in map order.
    ``source_observed_indices`` must be derived from source-visible declaration
    and instance structure, independently of the exported element list. Source
    and data hash binding plus candidate proxy definitions remain the caller's
    responsibility and should be recorded in its mapping ledger.
    """
    if not isinstance(reference_metadata, dict):
        raise CoordinateMetadataError("reference metadata must be an object")
    if not isinstance(reference_metadata.get("observables"), list):
        raise CoordinateMetadataError("reference observables must be an explicit list")
    if not isinstance(coordinate_maps, (list, tuple)):
        raise CoordinateMetadataError("coordinate maps must be a sequence")
    if not isinstance(source_observed_indices, dict):
        raise CoordinateMetadataError("source observed indices must be an explicit mapping")
    copied = deepcopy(reference_metadata)
    records = {}
    for record in copied["observables"]:
        if not isinstance(record, dict) or not isinstance(record.get("name"), str):
            raise CoordinateMetadataError("each reference observable needs a name")
        name = record["name"]
        if name in records:
            raise CoordinateMetadataError(f"duplicate reference observable {name!r}")
        records[name] = record
    seen_names = set()
    for mapping in coordinate_maps:
        if not isinstance(mapping, dict):
            raise CoordinateMetadataError("each coordinate map must be an object")
        name = mapping.get("reference_name")
        if not isinstance(name, str) or name not in records:
            raise CoordinateMetadataError(f"coordinate map names unknown reference {name!r}")
        if name in seen_names:
            raise CoordinateMetadataError(f"duplicate coordinate map for reference {name!r}")
        seen_names.add(name)
        record = records[name]
        shape = _shape(record.get("shape"), f"reference {name}")
        pairs = mapping.get("coordinates")
        if not isinstance(pairs, list):
            raise CoordinateMetadataError("coordinate map coordinates must be a list")
        mapped = []
        for pair in pairs:
            if not isinstance(pair, dict):
                raise CoordinateMetadataError("each coordinate entry must be an object")
            mapped.append(_index(pair.get("reference_index"), shape, "mapped reference index"))
        if len(mapped) != len(set(mapped)):
            raise CoordinateMetadataError(f"coordinate map repeats a reference cell for {name!r}")
        elements = record.get("elements")
        if not isinstance(elements, list):
            raise CoordinateMetadataError(f"reference {name!r} elements must be a list")
        exported = []
        for element in elements:
            if not isinstance(element, dict):
                raise CoordinateMetadataError("each exported reference element must be an object")
            exported.append(_index(element.get("index"), shape, "exported reference index"))
        if len(exported) != len(set(exported)):
            raise CoordinateMetadataError(f"reference {name!r} repeats an exported cell")
        if set(mapped) != set(exported):
            raise CoordinateMetadataError(
                f"map must cover exactly exported cells for {name!r}; "
                f"missing={sorted(set(exported) - set(mapped))}, "
                f"extra={sorted(set(mapped) - set(exported))}")
        raw_source_indices = source_observed_indices.get(name)
        if not isinstance(raw_source_indices, (list, tuple)):
            raise CoordinateMetadataError(f"source observed coordinates are missing for {name!r}")
        source_indices = [_index(value, shape, "source observed index")
                          for value in raw_source_indices]
        if len(source_indices) != len(set(source_indices)):
            raise CoordinateMetadataError(f"source observed coordinates repeat for {name!r}")
        if set(source_indices) != set(mapped):
            raise CoordinateMetadataError(f"source and map coordinate coverage disagree for {name!r}")
        cardinality = 1
        for size in shape:
            cardinality *= size
        if len(mapped) < cardinality:
            record["sparse"] = True
            record["observed_indices"] = [list(coord) for coord in mapped]
    return copied
