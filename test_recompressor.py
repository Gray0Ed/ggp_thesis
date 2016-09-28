import os
import sys
from os.path import isfile

RECOMPRESSOR_INPUTS_D = 'test/recompressor_inputs/'
RECOMPRESSOR_OUTPUTS_D = 'test/recompressor_outputs/'

COMMAND_CHAIN = [
    ("python simplify_by_sancho.py {0} {1} >{2} 2>{3}", "simplified"),
    ("./rule_engine/reprinter {0} {1} >{2} 2>{3}", "first_reprinted"),
    #("python flatten_by_sancho.py {0} {1} >{2} 2>{3}", "flattened"),
    ("./rule_engine/flatten {0} {1} >{2} 2>{3}", "flattened"),
    ("./rule_engine/reprinter {0} {1} >{2} 2>{3}", "reprinted"),
    ("time ./rule_engine/recompressor {0} {1} >{2} 2>{3}", "recompressed"),
]

def run_cmd(cmd_s):
    print cmd_s
    return os.system(cmd_s)


def run_cmd_fail(cmd_s):
    if run_cmd(cmd_s):
        raise Exception("Command:\n%s\nfailed." % cmd_s)


def make():
    if run_cmd("cd rule_engine && make") != 0:
        raise Exception("compilation failed")


def main():
    os.system('mkdir -p test/recompressor_outputs')
    global inputs
    if len(sys.argv) > 1:
        inputs = sys.argv[1:]
    else:
        raise Exception("No inputs provided")
    make()

    for inpf in inputs:
        cmd_input = None
        out_dir = (RECOMPRESSOR_OUTPUTS_D + inpf + '/')
        run_cmd("mkdir -p %s" % out_dir)
        for command_pattern, output_suffix in COMMAND_CHAIN:
            if cmd_input is None:
                cmd_input = RECOMPRESSOR_INPUTS_D + inpf
                if not isfile(cmd_input):
                    raise Exception("file %s does not exist" % cmd_input)
            cmd_output = out_dir + output_suffix
            cmd_stdout = cmd_output + '.stdout'
            cmd_stderr = cmd_output + '.stderr'
            cmd = command_pattern.format(
                    cmd_input, cmd_output, 
                    cmd_stdout, cmd_stderr)
            run_cmd_fail(cmd)
            cmd_input = cmd_output


if __name__ == '__main__':
    main()
