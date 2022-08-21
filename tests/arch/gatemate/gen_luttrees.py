from random import Random

def main():
    r = Random(1)

    N = 750
    with open("tests/arch/gatemate/luttrees.v", "w") as v:
        print(f"module luttrees(input [{N-1}:0] a, b, c, d, e, output [{N-1}:0] q);", file=v)
        for i in range(N):
            def f():
                return r.choice(["&", "|", "^"])

            def a(x):
                return f"({r.choice(['', '!'])}{x}[{i}])"

            # Bias towards testing bigger functions
            k = r.choice([2, 3, 4, 4, 4, 5, 5, 5])
            if k == 2:
                expr = f"{a('a')}{f()}{a('b')}"
            elif k == 3:
                expr = f"({a('a')}{f()}{a('b')}){f()}{a('c')}"
            elif k == 4:
                # Two types of 4-input function
                if r.choice([False, True]):
                    expr = f"(({a('a')}{f()}{a('b')}){f()}{a('c')}){f()}{a('d')}"
                else:
                    expr = f"({a('a')}{f()}{a('b')}){f()}({a('c')}{f()}{a('d')})"
            elif k == 5:
                expr = f"(({a('a')}{f()}{a('b')}){f()}({a('c')}{f()}{a('d')})){f()}{a('e')}"
            print(f"    assign q[{i}] = {expr};", file=v)
        print("endmodule", file=v)
    with open("tests/arch/gatemate/luttrees.ys", "w") as s:
        print(f"""
read_verilog luttrees.v
design -save read

hierarchy -top luttrees
proc
equiv_opt -async2sync -assert -map +/gatemate/cells_sim.v synth_gatemate -noiopad -luttree -nomx4 -nomx8 # equivalency check
design -load postopt # load the post-opt design (otherwise equiv_opt loads the pre-opt design)
cd luttrees # Constrain all select calls below inside the top module

select -assert-count {N} t:CC_LUT2 t:CC_L2T4 t:CC_L2T5 %%
select -assert-none t:CC_LUT2 t:CC_L2T4 t:CC_L2T5 %% t:* %D
""", file=s)

if __name__ == '__main__':
    main()
