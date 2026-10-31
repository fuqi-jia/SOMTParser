"""Extract a sufficient ordered-prefix core from unchanged XCSP XML bytes.

Only uniform integer arrays, binary lt/ne intensions and zero-based variable
element constraints are consumed. Each generated fact carries its XML origin.
Other constraints remain outside the sufficient UNSAT core.
"""
import hashlib
import re
import xml.etree.ElementTree as ET

import z3


def extract_ordered_prefix_xml(xml, row_count, row_name="x", index_name="pos",
                               left_name="pos1", right_name="pos2"):
    if not isinstance(xml, bytes):
        raise ValueError("original XML bytes required")
    root = ET.fromstring(xml)
    variables, constraints = root.find("variables"), root.find("constraints")
    if (root.tag != "instance" or root.get("format") != "XCSP3"
            or root.get("type") not in {"CSP", "COP"}
            or variables is None or constraints is None):
        raise ValueError("XCSP instance with variables and constraints required")
    arrays = {}
    needed = {row_name, index_name, left_name, right_name}
    for element in variables:
        name = element.get("id")
        if name not in needed:
            continue
        if name in arrays or element.tag != "array" or list(element):
            raise ValueError("uniform unique arrays required")
        if set(element.attrib) - {"id", "size", "note", "class"}:
            raise ValueError("unsupported array attributes")
        size = element.get("size", "")
        if not re.fullmatch(r"(?:\[\d+\])+", size):
            raise ValueError("explicit array dimensions required")
        dimensions = tuple(map(int, re.findall(r"\d+", size)))
        domain = re.fullmatch(r"\s*(-?\d+)\.\.(-?\d+)\s*", element.text or "")
        if domain is None:
            raise ValueError("closed integer array domains required")
        low, high = map(int, domain.groups())
        if low > high:
            raise ValueError("nonempty original array domain required")
        arrays[name] = (dimensions, low, high, hashlib.sha256(ET.tostring(element)).hexdigest())
    if set(arrays) != needed or len(arrays[row_name][0]) != 2:
        raise ValueError("all four declared arrays required")
    total, length = arrays[row_name][0]
    if not isinstance(row_count, int) or isinstance(row_count, bool) or not 1 <= row_count <= total:
        raise ValueError("invalid selected row count")
    if any(arrays[name][0] != (total, total) for name in needed - {row_name}):
        raise ValueError("pair arrays must match row count")
    selected, facts, origins = {}, [], []
    def variable(name, array):
        value = z3.Int(name)
        selected[name] = value
        _, low, high, array_hash = arrays[array]
        for bound in (value >= low, value <= high):
            facts.append(bound)
            origins.append(dict(kind="uniform-array-domain", array=array, coordinate=name,
                                array_xml_sha256=array_hash))
        return value
    rows = [[variable("%s[%d][%d]" % (row_name, i, j), row_name)
             for j in range(length)] for i in range(row_count)]
    pairs = {(i, j): tuple(variable("%s[%d][%d]" % (name, i, j), name)
                          for name in (index_name, left_name, right_name))
             for i in range(row_count) for j in range(i+1, row_count)}
    def consume(element, args, origin):
        def text(child):
            if child is None:
                return ""
            source = child.text or ""
            def replace(match):
                index = int(match.group(1))
                if args is None or index >= len(args):
                    raise ValueError("unbound group parameter")
                return args[index]
            return re.sub(r"%(\d+)", replace, source).strip()
        if element.tag == "intension":
            expression = re.sub(r"\s+", "", text(element))
            match = re.fullmatch(r"(lt|ne)\(([^,()]+),([^,()]+)\)", expression)
            if match is None:
                return
            operation, left, right = match.groups()
            if left not in selected or right not in selected:
                return
            if list(element) or set(element.attrib) - {"id", "note", "class"}:
                raise ValueError("unsupported selected intension")
            fact = selected[left] < selected[right] if operation == "lt" else selected[left] != selected[right]
        elif element.tag == "element":
            if len(element) != 3 or [child.tag for child in element] != ["list", "index", "value"]:
                return
            if any(list(child) for child in element):
                raise ValueError("plain text element children required")
            items, index, value = (text(child) for child in element)
            match = re.fullmatch(re.escape(row_name) + r"\[(\d+)\]\[\]", items)
            if match is None or int(match.group(1)) >= row_count or index not in selected or value not in selected:
                return
            if set(element.attrib) - {"id", "note", "class", "startIndex"}:
                raise ValueError("unsupported selected element attributes")
            if element.get("startIndex", "0") != "0":
                raise ValueError("only original zero-based elements supported")
            if element[0].attrib or element[2].attrib or set(element[1].attrib) - {"rank"}:
                raise ValueError("unsupported selected element children")
            if element[1].get("rank", "any") != "any":
                raise ValueError("only any-rank element supported")
            row = rows[int(match.group(1))]
            fact = z3.Or(*(z3.And(selected[index] == k, selected[value] == x) for k, x in enumerate(row)))
        else:
            return
        facts.append(fact)
        origins.append(dict(origin, template_xml_sha256=hashlib.sha256(ET.tostring(element)).hexdigest(),
                            arguments=args))
    for index, element in enumerate(constraints):
        if element.tag == "group":
            if not len(element):
                continue
            template = element[0]
            if template.tag not in {"element", "intension"}:
                continue
            if set(element.attrib) - {"id", "note", "class"}:
                raise ValueError("only unconditional original groups supported")
            for argument_index, argument in enumerate(element[1:], 1):
                if argument.tag != "args" or list(argument) or argument.attrib:
                    raise ValueError("plain group arguments required")
                consume(template, (argument.text or "").split(),
                        dict(kind="group-instance", constraint_index=index, argument_index=argument_index))
        else:
            consume(element, None, dict(kind="direct-constraint", constraint_index=index))
    return facts, rows, pairs, dict(source_raw_sha256=hashlib.sha256(xml).hexdigest(),
                                    original_xml_bytes=len(xml), row_count=row_count,
                                    row_length=length, declared_rows=total,
                                    facts=len(facts), origins=origins,
                                    selected_coordinate_names=sorted(selected))
