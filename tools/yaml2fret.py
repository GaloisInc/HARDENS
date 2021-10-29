#!/usr/bin/env python3

import yaml
import argparse
import json
import subprocess
import sys

def getArgs():
    parser = argparse.ArgumentParser(description='Generate importable FRET requirements.')
    parser.add_argument('source', metavar='FILE', type=open)
    parser.add_argument('dest_requirements', metavar='FILE', type=argparse.FileType('w'))
    parser.add_argument('dest_variables', metavar='FILE', type=argparse.FileType('w'))

    args = parser.parse_args()

    return args

def getSemantics(txt):
    cmd = subprocess.run(["node", "tools/generate_semantics.js", txt], capture_output=True)
    if cmd.returncode == 0:
        return json.loads(cmd.stdout)['collectedSemantics']
    else:
        print(cmd.stderr)
        return None

def instantiate(req0, env={}):
    if 'for' in req0:
        out = []
        i = req0['for']
        rng = req0['in']
        for x in rng:
            env = dict(env)
            env[i] = x
            for sub_req in req0['requirements']:
                for req in instantiate(sub_req, env=env):
                    if 'parent_reqid' not in req:
                        req['parent_reqid'] = ''

                    if 'rationale' not in req:
                        req['rationale'] = ''

                    fulltext = req['fulltext']
                    req_id   = req['reqid']
                    rationale = req['rationale']
                    parent    = req['parent_reqid']

                    text_x = fulltext.format(**env)
                    req_id_x = req_id.format(**env)
                    rationale_x = rationale.format(**env)
                    parent_x = parent.format(**env)
                    req_x = dict(req)
                    req_x['fulltext'] = text_x
                    req_x['rationale'] = rationale_x
                    req_x['reqid'] = req_id_x
                    req_x['parent_reqid'] = parent_x

                    sem = getSemantics(req_x['fulltext'])
                    if sem is not None:
                        req_x['semantics'] = sem
                        out.append(req_x)
                    else:
                        sys.exit(1)

        return out
    else:
        return [req0]

def instantiate_var(v,env={}):
    out = []
    if 'for' in v:
        rng = v['in']
        env = dict(env)
        for x in rng:
            env[v['for']] = x
            for sub_v in v['variables']:
                out.extend(instantiate_var(sub_v, env))
    else:
        out_var = {}
        out_var['variable_name'] = v['name'].format(**env)
        out_var['dataType'] = v['type']
        out_var['idType'] = v['mtype']
        out_var['completed'] = True
        out_var['modeldoc'] = False
        out = [out_var]
    return out

def goVariables(vs, needed_vars, f):
    out = []
    for v in vs:
        out.extend(instantiate_var(v))
    var_vars = {v['variable_name'] for v in out}
    unused = var_vars - needed_vars
    for u in unused:
        print(f"Unused variable: {u}", file=sys.stderr)
    undefined = needed_vars - var_vars
    for u in undefined:
        print(f"Undefined variable: {u}", file=sys.stderr)
    json.dump(out, f, indent=2)

def main():
    args = getArgs()
    inp = yaml.load(args.source, yaml.Loader)
    out = []
    prj = inp['project']

    for req in inp['requirements']:
        for inst in instantiate(req):
            inst['project'] = prj
            out.append(inst)

    req_vars = {v for r in out for v in r['semantics']['variables']}

    json.dump(out, args.dest_requirements, indent=2)

    if 'variables' in inp:
        goVariables(inp['variables'], req_vars, args.dest_variables)

if __name__ == "__main__":
    main()
