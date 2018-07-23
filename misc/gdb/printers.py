import gdb.printing


def std_vector_at(v, i):
    """Get the gdb.Value object from a std::vector for a given index."""
    # Find a pretty printer for the std::vector and then find the child
    # which matches our index.
    ni = '[%d]' % i
    vprinter = gdb.default_visualizer(v)
    value = None
    for n, v in vprinter.children():
        if n == ni:
            value = v
            break

    # Return either the child object or None
    return value


class IdStringPrinter:
    """Print a IdString object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        return []

    def type_hint(self):
        return 'string'

    @property
    def index(self):
        return int(self.val["index_"])

    def get_value(self):
        # Get the actual string from the global id storage which is a
        # std::vector
        return std_vector_at(self.val["global_id_storage_"], self.index)

    def to_string(self):
        value = self.get_value()
        vstr = "???"
        if value is not None:
            vprinter = gdb.default_visualizer(value)
            if vprinter is not None:
                vstr = '"%s"' % vprinter.to_string()
            else:
                vstr = '"%s"' % value.string()
        return '(%d)%s' % (self.index, vstr)


def build_pretty_printer():
    pp = gdb.printing.RegexpCollectionPrettyPrinter(
        "yosys")
    pp.add_printer('IdString', '^Yosys::RTLIL::IdString$', IdStringPrinter)
    return pp
