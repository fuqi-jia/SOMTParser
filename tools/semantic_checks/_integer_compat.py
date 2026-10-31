"""Integer operations shared by semantic checks on Python 3.9 and newer."""


def _portable_bit_count(value: int) -> int:
    # bin retains a minus sign for negative inputs; it does not affect the
    # number of one bits, matching int.bit_count's absolute-value semantics.
    return bin(value).count("1")


bit_count = getattr(int, "bit_count", _portable_bit_count)
