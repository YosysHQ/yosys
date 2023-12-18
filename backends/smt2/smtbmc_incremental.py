from collections import defaultdict
import json
import typing
from functools import partial

if typing.TYPE_CHECKING:
    import smtbmc
else:
    import sys

    smtbmc = sys.modules["__main__"]


class InteractiveError(Exception):
    pass


class Incremental:
    def __init__(self):
        self.traceidx = 0

        self.state_set = set()
        self.map_cache = {}

        self._cached_hierwitness = {}
        self._witness_index = None

        self._yw_constraints = {}

    def setup(self):
        generic_assert_map = smtbmc.get_assert_map(
            smtbmc.topmod, "state", smtbmc.topmod
        )
        self.inv_generic_assert_map = {
            tuple(data[1:]): key for key, data in generic_assert_map.items()
        }
        assert len(self.inv_generic_assert_map) == len(generic_assert_map)

    def print_json(self, **kwargs):
        print(json.dumps(kwargs), flush=True)

    def print_msg(self, msg):
        self.print_json(msg=msg)

    def get_cached_assert(self, step, name):
        try:
            assert_map = self.map_cache[step]
        except KeyError:
            assert_map = self.map_cache[step] = smtbmc.get_assert_map(
                smtbmc.topmod, f"s{step}", smtbmc.topmod
            )
        return assert_map[self.inv_generic_assert_map[name]][0]

    def arg_step(self, cmd, declare=False, name="step", optional=False):
        step = cmd.get(name, None)
        if step is None and optional:
            return None
        if not isinstance(step, int):
            if optional:
                raise InteractiveError(f"{name} must be an integer")
            else:
                raise InteractiveError(f"integer {name} argument required")
        if declare and step in self.state_set:
            raise InteractiveError(f"step {step} already declared")
        if not declare and step not in self.state_set:
            raise InteractiveError(f"step {step} not declared")
        return step

    def expr_arg_len(self, expr, min_len, max_len=-1):
        if max_len == -1:
            max_len = min_len
        arg_len = len(expr) - 1

        if min_len is not None and arg_len < min_len:
            if min_len == max_len:
                raise (
                    f"{json.dumps(expr[0])} expression must have "
                    f"{min_len} argument{'s' if min_len != 1 else ''}"
                )
            else:
                raise (
                    f"{json.dumps(expr[0])} expression must have at least "
                    f"{min_len} argument{'s' if min_len != 1 else ''}"
                )
        if max_len is not None and arg_len > max_len:
            raise (
                f"{json.dumps(expr[0])} expression can have at most "
                f"{min_len} argument{'s' if max_len != 1 else ''}"
            )

    def expr_step(self, expr, smt_out):
        self.expr_arg_len(expr, 1)
        step = expr[1]
        if step not in self.state_set:
            raise InteractiveError(f"step {step} not declared")
        smt_out.append(f"s{step}")
        return "module", smtbmc.topmod

    def expr_mod_constraint(self, expr, smt_out):
        self.expr_arg_len(expr, 1)
        position = len(smt_out)
        smt_out.append(None)
        arg_sort = self.expr(expr[1], smt_out, required_sort=["module", None])
        module = arg_sort[1]
        suffix = expr[0][3:]
        smt_out[position] = f"(|{module}{suffix}| "
        smt_out.append(")")
        return "Bool"

    def expr_mod_constraint2(self, expr, smt_out):
        self.expr_arg_len(expr, 2)

        position = len(smt_out)
        smt_out.append(None)
        arg_sort = self.expr(expr[1], smt_out, required_sort=["module", None])
        smt_out.append(" ")
        self.expr(expr[2], smt_out, required_sort=arg_sort)
        module = arg_sort[1]
        suffix = expr[0][3:]
        smt_out[position] = f"(|{module}{suffix}| "
        smt_out.append(")")
        return "Bool"

    def expr_not(self, expr, smt_out):
        self.expr_arg_len(expr, 1)

        smt_out.append("(not ")
        self.expr(expr[1], smt_out, required_sort="Bool")
        smt_out.append(")")
        return "Bool"

    def expr_eq(self, expr, smt_out):
        self.expr_arg_len(expr, 2)

        smt_out.append("(= ")
        arg_sort = self.expr(expr[1], smt_out)
        if (
            smtbmc.smt.unroll
            and isinstance(arg_sort, (list, tuple))
            and arg_sort[0] == "module"
        ):
            raise InteractiveError("state equality not supported in unroll mode")

        smt_out.append(" ")
        self.expr(expr[2], smt_out, required_sort=arg_sort)
        smt_out.append(")")
        return "Bool"

    def expr_andor(self, expr, smt_out):
        if len(expr) == 1:
            smt_out.push({"and": "true", "or": "false"}[expr[0]])
        elif len(expr) == 2:
            arg_sort = self.expr(expr[1], smt_out)
            if arg_sort != "Bool":
                raise InteractiveError(
                    f"arguments of {json.dumps(expr[0])} must have sort Bool"
                )
        else:
            sep = f"({expr[0]} "
            for arg in expr[1:]:
                smt_out.append(sep)
                sep = " "
                self.expr(arg, smt_out, required_sort="Bool")
            smt_out.append(")")
        return "Bool"

    def expr_yw(self, expr, smt_out):
        if len(expr) == 2:
            name = None
            step = expr[1]
        elif len(expr) == 3:
            name = expr[1]
            step = expr[2]

        if step not in self.state_set:
            raise InteractiveError(f"step {step} not declared")

        if name not in self._yw_constraints:
            raise InteractiveError(f"no yw file loaded as name {name!r}")

        constraints = self._yw_constraints[name].get(step, [])

        if len(constraints) == 0:
            smt_out.append("true")
        elif len(constraints) == 1:
            smt_out.append(constraints[0])
        else:
            sep = "(and "
            for constraint in constraints:
                smt_out.append(sep)
                sep = " "
                smt_out.append(constraint)
            smt_out.append(")")

        return "Bool"

    def expr_smtlib(self, expr, smt_out):
        self.expr_arg_len(expr, 2)

        smtlib_expr = expr[1]
        sort = expr[2]

        if not isinstance(smtlib_expr, str):
            raise InteractiveError(
                "raw SMT-LIB expression has to be a string, "
                f"got {json.dumps(smtlib_expr)}"
            )

        if not isinstance(sort, str):
            raise InteractiveError(
                f"raw SMT-LIB sort has to be a string, got {json.dumps(sort)}"
            )

        smt_out.append(smtlib_expr)
        return sort

    def expr_label(self, expr, smt_out):
        if len(expr) != 3:
            raise InteractiveError(
                f'expected ["!", label, sub_expr], got {json.dumps(expr)}'
            )
        label = expr[1]
        subexpr = expr[2]

        if not isinstance(label, str):
            raise InteractiveError(f"expression label has to be a string")

        smt_out.append("(! ")
        smt_out.appedd(label)
        smt_out.append(" ")

        sort = self.expr(subexpr, smt_out)

        smt_out.append(")")

        return sort

    expr_handlers = {
        "step": expr_step,
        "mod_h": expr_mod_constraint,
        "mod_is": expr_mod_constraint,
        "mod_i": expr_mod_constraint,
        "mod_a": expr_mod_constraint,
        "mod_u": expr_mod_constraint,
        "mod_t": expr_mod_constraint2,
        "not": expr_not,
        "and": expr_andor,
        "or": expr_andor,
        "=": expr_eq,
        "yw": expr_yw,
        "smtlib": expr_smtlib,
        "!": expr_label,
    }

    def expr(self, expr, smt_out, required_sort=None):
        if not isinstance(expr, (list, tuple)) or not expr:
            raise InteractiveError(
                f"expression must be a non-empty JSON array, found: {json.dumps(expr)}"
            )
        name = expr[0]

        handler = self.expr_handlers.get(name)
        if handler:
            sort = handler(self, expr, smt_out)

            if required_sort is not None:
                if isinstance(required_sort, (list, tuple)):
                    if (
                        not isinstance(sort, (list, tuple))
                        or len(sort) != len(required_sort)
                        or any(
                            r is not None and r != s
                            for r, s in zip(required_sort, sort)
                        )
                    ):
                        raise InteractiveError(
                            f"required sort {json.dumps(required_sort)} "
                            f"found sort {json.dumps(sort)}"
                        )
            return sort
        raise InteractiveError(f"unknown expression {json.dumps(expr[0])}")

    def expr_smt(self, expr, required_sort):
        smt_out = []
        self.expr(expr, smt_out, required_sort=required_sort)
        out = "".join(smt_out)
        return out

    def cmd_new_step(self, cmd):
        step = self.arg_step(cmd, declare=True)
        self.state_set.add(step)
        smtbmc.smt_state(step)

    def cmd_assert(self, cmd):
        name = cmd.get("cmd")

        assert_fn = {
            "assert_antecedent": smtbmc.smt_assert_antecedent,
            "assert_consequent": smtbmc.smt_assert_consequent,
            "assert": smtbmc.smt_assert,
        }[name]

        assert_fn(self.expr_smt(cmd.get("expr"), "Bool"))

    def cmd_push(self, cmd):
        smtbmc.smt_push()

    def cmd_pop(self, cmd):
        smtbmc.smt_pop()

    def cmd_check(self, cmd):
        return smtbmc.smt_check_sat()

    def cmd_smtlib(self, cmd):
        command = cmd.get("command")
        if not isinstance(command, str):
            raise InteractiveError(
                f"raw SMT-LIB command must be a string, found {json.dumps(command)}"
            )
        smtbmc.smt.write(command)

    def cmd_design_hierwitness(self, cmd=None):
        allregs = (cmd is None) or bool(cmd.get("allreges", False))
        if self._cached_hierwitness[allregs] is not None:
            return self._cached_hierwitness[allregs]
        inits, seqs, clocks, mems = smtbmc.smt.hierwitness(smtbmc.topmod, allregs)
        self._cached_hierwitness[allregs] = result = dict(
            inits=inits, seqs=seqs, clocks=clocks, mems=mems
        )
        return result

    def cmd_write_yw_trace(self, cmd):
        steps = cmd.get("steps")
        allregs = bool(cmd.get("allregs", False))

        if steps is None:
            steps = sorted(self.state_set)

        path = cmd.get("path")

        smtbmc.write_yw_trace(steps, self.traceidx, allregs=allregs, filename=path)

        if path is None:
            self.traceidx += 1

    def cmd_read_yw_trace(self, cmd):
        steps = cmd.get("steps")
        path = cmd.get("path")
        name = cmd.get("name")
        skip_x = cmd.get("skip_x", False)
        if path is None:
            raise InteractiveError("path required")

        constraints = defaultdict(list)

        if steps is None:
            steps = sorted(self.state_set)

        map_steps = {i: int(j) for i, j in enumerate(steps)}

        last_step = smtbmc.ywfile_constraints(
            path, constraints, map_steps=map_steps, skip_x=skip_x
        )

        self._yw_constraints[name] = {
            map_steps.get(i, i): [smtexpr for cexfile, smtexpr in constraint_list]
            for i, constraint_list in constraints.items()
        }

        return dict(last_step=last_step)

    def cmd_ping(self, cmd):
        return cmd

    cmd_handlers = {
        "new_step": cmd_new_step,
        "assert": cmd_assert,
        "assert_antecedent": cmd_assert,
        "assert_consequent": cmd_assert,
        "push": cmd_push,
        "pop": cmd_pop,
        "check": cmd_check,
        "smtlib": cmd_smtlib,
        "design_hierwitness": cmd_design_hierwitness,
        "write_yw_trace": cmd_write_yw_trace,
        "read_yw_trace": cmd_read_yw_trace,
        "ping": cmd_ping,
    }

    def handle_command(self, cmd):
        if not isinstance(cmd, dict) or "cmd" not in cmd:
            raise InteractiveError('object with "cmd" key required')

        name = cmd.get("cmd", None)

        handler = self.cmd_handlers.get(name)
        if handler:
            return handler(self, cmd)
        else:
            raise InteractiveError(f"unknown command: {name}")

    def mainloop(self):
        self.setup()
        while True:
            try:
                cmd = input().strip()
                if not cmd or cmd.startswith("#") or cmd.startswith("//"):
                    continue
                try:
                    cmd = json.loads(cmd)
                except json.decoder.JSONDecodeError as e:
                    self.print_json(err=f"invalid JSON: {e}")
                    continue
            except EOFError:
                break

            try:
                result = self.handle_command(cmd)
            except InteractiveError as e:
                self.print_json(err=str(e))
                continue
            except Exception as e:
                self.print_json(err=f"internal error: {e}")
                raise
            else:
                self.print_json(ok=result)
