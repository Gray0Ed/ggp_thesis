import os
import sys
import re


cmd = "java -classpath {class_path} grayed.MyFlattenerTool {arg_1} {arg_2}"

def generate_classpath():
    build_data = open(
        '/home/j/projects/ggp/oss_player/sancho/ggp-base/build.xml', 'r').read()
    return ':'.join(['/home/j/projects/ggp/oss_player/sancho/ggp-base/' + x for x in 
            re.findall('pathelement location=\"(.*)\"', build_data)])

cmd = cmd.format(class_path=generate_classpath(), arg_1=sys.argv[1], arg_2=sys.argv[2])
#print cmd
os.system(cmd)
