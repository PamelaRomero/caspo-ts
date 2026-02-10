#!/usr/bin/env python
import subprocess

from .crossvar import globalvariables

U_GENERAL = "general"
U_ASYNC = "asynchronous"

MODES = [U_GENERAL, U_ASYNC]


def make_smv(dataset, network, destfile, update: str = U_GENERAL):
    
    dvars = dataset.setup.nodes.union(network.variables()) # nodes referenced in dataset
    varying_nodes = set([node for node, _ in network.formulas_iter()]) # nodes for which a function is defined
    constants = dvars.difference(varying_nodes) # nodes with no function (i.e., constant value)

    dirty_start = set()
    for exp in dataset.experiments.values():
        if 0 not in exp.obs:
            dirty_start.update(dataset.readout)
            break
        else:
            readouts0 = set(exp.obs[0].keys())
            dirty_start.update(dataset.readout.difference(readouts0))
    clampable = varying_nodes.intersection(dataset.inhibitors.union(dataset.stimulus))

    smv = open(destfile, "w")
    smv.write("MODULE main\n")
    smv.write("\nVAR\n")
    smv.write("\tstart: boolean;\n")
    for n in constants:
        smv.write("\tn_%s: word[2];\n" % n)  # the variable type is changed to word
    for n in varying_nodes:
        smv.write("\tn_%s: word[2];\n" % n)  # the variable type is changed to word
        smv.write("\tu_%s: boolean;\n" % n)
        if n in clampable:
            smv.write("\tC_%s: {0,1,2,-1};\n" % n)
    for n in dirty_start:
        smv.write("\tdirty_%s: boolean;\n" % n)

    smv.write("\nASSIGN\n")
    smv.write("next(start) := FALSE;\n")
    
    for n in dirty_start:
        smv.write("next(dirty_%s) := FALSE;\n" % n)
    
    for n in constants:
        smv.write("next(n_%s) := n_%s;\n" % (n, n))
    
    for n in varying_nodes:
        smv.write("next(n_%s) := case " % n)
        if n not in dataset.readout:
            smv.write("start: 0ud2_0; ")  # smv.write("start: word[2]; ") Note that here it is only initialized with a value of 0, but it should be with any value
        elif n in dirty_start:
            smv.write("start & dirty_%s: {0ud2_0, 0ud2_1, 0ud2_2}; " % n) # unknown initial value can be 0, 1, or 2  {0ud2_0, 0ud2_1, 0ud2_2}
        # If it is updated and the logical function is TRUE, then the node will have a value of 1. 
        smv.write("((u_1_%s=0ud2_1) & (F_%s=0ud2_1)): 0ud2_1; ((u_1_%s=0ud2_1) & (F_%s=0ud2_0)): 0ud2_0; ((u_1_%s=0ud2_1) & (F_%s=0ud2_2)): 0ud2_2; TRUE: n_%s; esac;\n" % (n, n, n, n, n, n, n)) # smv.write("u_%s: F_%s; TRUE: n_%s; esac;\n" % (n, n, n)) 
        
        if n in clampable:
            smv.write("next(C_%s) := C_%s;\n" % (n, n))

    smv.write("\nDEFINE\n")
  
    def int_to_binary(a):
        if a == 1:
            value = "0ud2_1" #"0b01"
        elif a == 2:
            value = "0ud2_2" #"0b10"
        else:
            value = "0ud2_0" #"0b00"
        return value
   
    def nusmv_of_literal(literal):
        var, sign = literal 
        return "%sn_%s" % ("!" if sign == -1 else "", var)

    def nusmv_of_clause(clause):
        expr = " & ".join(map(nusmv_of_literal, clause))
        if len(clause) > 1:
            return "(%s)" % expr
        return expr

    def nusmv_of_clauses(clauses):
        if len(clauses) == 0:
            return "FALSE"
        return " | ".join(map(nusmv_of_clause, clauses))

   
    for n, clauses in network.formulas_iter():
        expr = nusmv_of_clauses(clauses)
        if n in clampable:
            smv.write("F_%s := case C_%s=0: %s; " % (n, n, expr))
            smv.write("C_%s=1: 0ud2_1; C_%s=2: 0ud2_2; C_%s=-1: 0ud2_0; esac;\n" % (n, n, n))
        else:
            smv.write("F_%s := %s;\n" % (n, expr))
        smv.write("u_1_%s := case u_%s : 0ud2_1; TRUE : 0ud2_0; esac;\n" % (n, n)) # convert the boolean u to a word

    for exp in dataset.experiments.values():
        setup = []
        
        for n, c in exp.mutations.items():  # enforce initial state of clamped nodes
            # compares the value of the node and if it matches, converts it to Boolean
            setup.append("%s(n_%s = %s)" % ("!" if c < 0 else "", n, int_to_binary(c))) 
        for n in clampable:  # specify clamping setting
            if n in exp.mutations:
                c = exp.mutations[n]
                setup.append("C_%s=%s" % (n, c))
            else:
                setup.append("C_%s=0" % n)
        # compares the value of the node and if it matches, converts it to Boolean
        smv.write("E%d_SETUP := (%s);\n" % (exp.id, " & ".join(setup))) 
        if 0 not in exp.obs:
            # compares the value of the node and if it matches, converts it to Boolean
            smv.write("E%d_T0 := (%s);\n" % (exp.id, t, " & ".join(["dirty_%s" % n for n in dirty_start]))) 
        for t, values in exp.obs.items():
            state = []
            for n, v in values.items():               
                state.append("%s(n_%s = %s)" % ("!" if not v else "", n, int_to_binary(v))) 
            if t == 0:
                for n in dirty_start:
                    neg = "!" if n not in values else ""
                    state.append("%sdirty_%s" % (neg, n))
            # compares the value of the node and if it matches, converts it to Boolean
            smv.write("E%d_T%d := %s;\n" % (exp.id, t, " & ".join(state)))
   

    fpconds = ["n_%s = F_%s" % (n, n) for n in varying_nodes]
   
    smv.write("FIXEDPOINTS := %s;\n" % " & ".join(fpconds))

    smv.write("\nTRANS\n")
    smv.write("  next(start) != start")
    #for n in varying_nodes:
        #smv.write("\n| next(n_%s) != n_%s" % (n, n))
        #smv.write("\n| next(u_%s) != u_%s" % (n, n))
    smv.write("\n| FIXEDPOINTS")
    smv.write(";\n")

    if update == U_ASYNC:
        for n in varying_nodes:
            cond = " & ".join(["!u_%s" % m for m in varying_nodes if m != n])
            smv.write("TRANS u_%s -> %s;\n" % (n, cond))

    smv.write("\nINIT\n")
    smv.write("(start")
    for n in varying_nodes:
        smv.write(" & !u_%s" % n)
    smv.write(");\n")
    smv.close()

    return destfile


def verify(dataset, network, destfile, *args, **kwargs):
    smvfile = make_smv(dataset, network, destfile, *args, **kwargs)

    def ctl_of_exp(exp):
        ts = list(sorted(exp.obs.keys()))
        ctl = "(E%d_SETUP & E%d_T0) -> " % (exp.id, exp.id)
        if ts[0] == 0:
            t0 = ts.pop(0)
            if not ts:
                return "TRUE"
        for t in ts:
            ctl += "EF (E%d_T%d & " % (exp.id, t)
        ctl = ctl[:-2] + ")" * len(ts)
        return "(%s)" % ctl

    wrote_expr0 = False
    for exp in dataset.experiments.values():
        if exp.id == 0 and not wrote_expr0:
            wrote_expr0 = True
            smv = open(destfile, "a")
            getexpr = ctl_of_exp(exp)
            smv.write("\nSPEC (\n  ")
            smv.write(getexpr)
            smv.write("\n);\n")
            smv.close()

        if exp.id != 0:
            smv = open(destfile, "rb") 
            pos = next = 0
            for line in smv:
                pos = next  # position of beginning of this line
                next += len(line)  # compute position of beginning of next line
            smv = open(destfile, "a")
            smv.truncate(pos)
            getexpr = ctl_of_exp(exp)
            smv.write("\n& " + getexpr)
            smv.write("\n);\n")
            smv.close()

        
        with open(destfile, "r", encoding="utf-8") as f:
            contenido = f.read()
        print(contenido)
    
        output = subprocess.check_output(["NuSMV", "-coi", "-dcx", smvfile])
        ret = output.strip().split()[-1].decode()
        if ret == "true":
            # print("The experiment %d is satisfiable" % exp.id)
            continue
        else:
            globalvariables.contraintonexp = exp.id
            # print("The experiment %d is not satisfiable" % exp.id)
            break
    return ret == "true"
    
