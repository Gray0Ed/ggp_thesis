import os
import sys
import itertools

TIMEOUT_SECONDS = str(2400)

input_dir = "test/flattener_inputs/"
output_dir = "test/flattener_outputs/"
sancho_simplified_prefix = "sancho_simpl_"
simplified_prefix = "simpl_"
reprinted_prefix = "reprinted_"
flat_prefix = {
    'sancho': 'sancho_flat_',
    'dbg': 'dbg_flat_',
    'opt': 'opt_flat_',
}
err_suffix = ".stderr"
out_suffix = ".stdout"

input_types = [
    #('amazons', ['opt', 'dbg']),
    ('amazons8x8', ['sancho', 'opt', 'dbg']),
    ('breakthrough', ['sancho', 'opt', 'dbg']),
    ('breakthroughSmall', ['sancho', 'opt', 'dbg']),
    ('checkers', ['opt', 'dbg']),
    ('checkersSmall', ['sancho', 'opt', 'dbg']),
    ('connect4', ['sancho', 'opt', 'dbg']),
    ('connect5', ['sancho', 'opt', 'dbg']),
    ('chess', ['opt', 'dbg']),
    ('reversi', ['opt', 'dbg']),
    ('ticTac', ['sancho', 'opt', 'dbg']),
]

inputs = []


def run_cmd(cmd_s):
    print cmd_s
    return os.system(cmd_s)


def run_cmd_fail(cmd_s):
    if run_cmd(cmd_s):
        raise Exception("Command:\n%s\nfailed." % cmd_s)


def make_rule_engine():
    if run_cmd("cd rule_engine && make") != 0:
        raise Exception("compilation failed")


def super_iterator(to_iterate):
    for t in to_iterate:
        yield t

def outname(input_name, flattener_name):
    return output_dir + flat_prefix[flattener_name] + input_name

def reprinted_outname(input_name, flattener_name):
    return (output_dir + reprinted_prefix + 
            flat_prefix[flattener_name] + input_name)


def main():
    global inputs
    if len(sys.argv) > 1:
        test_names = sys.argv[1:]
        inputs = [inpt for inpt in input_types if inpt[0] in test_names]
    else:
        inputs = input_types
    make_rule_engine()
    for inpfn, flatteners in inputs:
        inpfn = inpfn + '.kif'
        inpf = input_dir + inpfn
        out_sancho_simpl = output_dir + sancho_simplified_prefix + inpfn
        out_simpl = output_dir + simplified_prefix + inpfn
        run_cmd_fail("python simplify_by_sancho.py %s %s" % (inpf, out_sancho_simpl))
        run_cmd_fail("./rule_engine/reprinter %s %s" % (out_sancho_simpl, out_simpl))
        for flattener in flatteners:
            out_flat = outname(inpfn, flattener)
            stdoutf = out_flat + out_suffix
            stderrf = out_flat + err_suffix
            reprintedf = reprinted_outname(inpfn, flattener)
            if flattener == "sancho":
                cmd_prefix = "python flatten_by_sancho.py"
            if flattener == "opt":
                cmd_prefix = "./rule_engine/opt_flatten"
            if flattener == "dbg":
                cmd_prefix = "./rule_engine/flatten"
            run_cmd_fail("time timeout %s %s %s %s > %s 2> %s" % (
                TIMEOUT_SECONDS, cmd_prefix, out_simpl, 
                out_flat, stdoutf, stderrf)
            )
            run_cmd_fail("./rule_engine/reprinter %s %s" % (out_flat, reprintedf))
            run_cmd_fail("mv %s %s" % (reprintedf, out_flat))
        if len(flatteners) <= 2:
            assert set(['opt', 'dbg']).issubset(set(flatteners))
            if run_cmd("diff %s %s" % (outname(inpfn, 'opt'), outname(inpfn, 'dbg'))):
                raise Exception("opt different than dbg!")
        if len(flatteners) == 3:
            assert set(flatteners) == set(['opt', 'dbg', 'sancho'])
            opt_outn = outname(inpfn, 'opt')
            san_outn = outname(inpfn, 'sancho')
            with open(opt_outn, 'r') as opt_out, open(san_outn, 'r') as san_out:
                opt_it = super_iterator(opt_out)
                san_it = super_iterator(san_out)
                opt_line = next(opt_it, None)
                san_line = next(san_it, None)
                while opt_line is not None and san_line is not None:
                    while san_line is not None and san_line < opt_line:
                        san_line = next(san_it, None)
                    if san_line is None or san_line > opt_line:
                        raise Exception("line:\n%s\nnot in %s" % (opt_line, san_outn))
                    opt_line = next(opt_it, None)
        print "GOOD"


if __name__ == '__main__':
    main()
