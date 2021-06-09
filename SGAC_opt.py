from z3 import *
import set_functions
import re
import time

set_param(max_width=3000)
set_param(max_depth=5000000000000000000000000)
set_param(max_args=100000000000000)
set_param(max_lines=10000000000000)
set_param(max_indent=1000000000000)

ts = time.time()

s = Solver()  # Declaring the Z3 solver and storing it to the variable s.

'''
Starting to describe the SETS and PROPERTIES clauses fo the B machine.
'''

# Creating the Subject Graph
V_SUB = DeclareSort('Vertex_Subject')  # Declaring a type 'Vertex_Subject' (Vertex of the Subject Graph)
# Adding the Graph Nodes
s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17,\
s18, s19 = Consts('s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 '
                  's18 s19', V_SUB)  # Creating the nodes s0 - s19 to the Subject Graph
# Defining that the nodes are distinct (s0 != s1 != s2 != ... != s19)
s.add(Distinct(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19))


V_RES = DeclareSort('Vertex_Resource')  # Declaring a type 'Vertex_Resource' (Vertex of the Resource Graph)
r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,\
r18, r19 = Consts('r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17'
                  ' r18 r19', V_RES)  # Creating the nodes r0 - r19 to the Resource Graph
# Defining that the elements are distinct (r1 != r2 != r3 != ... != r19)
s.add(Distinct(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19))

Sub_Graph = Function('Subject_Graph', V_SUB, V_SUB, BoolSort())  # Declaring the Subject Graph
# Making a initialisation of the Graph
#auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)
s.add(Sub_Graph(s2, s1), Sub_Graph(s3, s0), Sub_Graph(s3, s1), Sub_Graph(s5, s0),
      Sub_Graph(s6, s4), Sub_Graph(s7, s0), Sub_Graph(s8, s1), Sub_Graph(s8, s2),
      Sub_Graph(s8, s3), Sub_Graph(s9, s1), Sub_Graph(s9, s2), Sub_Graph(s10, s2),
      Sub_Graph(s10, s6), Sub_Graph(s10, s8), Sub_Graph(s11, s4), Sub_Graph(s11, s10),
      Sub_Graph(s12, s0), Sub_Graph(s12, s6), Sub_Graph(s12, s7), Sub_Graph(s12, s9),
      Sub_Graph(s13, s0), Sub_Graph(s13, s2), Sub_Graph(s13, s4), Sub_Graph(s13, s7),
      Sub_Graph(s14, s0), Sub_Graph(s14, s4), Sub_Graph(s14, s11), Sub_Graph(s14, s13),
      Sub_Graph(s15, s1), Sub_Graph(s15, s6), Sub_Graph(s15, s12), Sub_Graph(s15, s14),
      Sub_Graph(s16, s7), Sub_Graph(s16, s9), Sub_Graph(s16, s11), Sub_Graph(s16, s14),
      Sub_Graph(s16, s15), Sub_Graph(s17, s1), Sub_Graph(s17, s7), Sub_Graph(s17, s11),
      Sub_Graph(s17, s16), Sub_Graph(s18, s2), Sub_Graph(s18, s3), Sub_Graph(s18, s5),
      Sub_Graph(s18, s6), Sub_Graph(s18, s7), Sub_Graph(s18, s17), Sub_Graph(s19, s0),
      Sub_Graph(s19, s1), Sub_Graph(s19, s6), Sub_Graph(s19, s13), Sub_Graph(s19, s15),
      Sub_Graph(s19, s16), Sub_Graph(s19, s18))
s.add(ForAll([auxSub1, auxSub2], If(Or(And(auxSub1 == s2, auxSub2 == s1), And(auxSub1 == s3, auxSub2 == s0),
                                       And(auxSub1 == s3, auxSub2 == s1), And(auxSub1 == s5, auxSub2 == s0),
                                       And(auxSub1 == s6, auxSub2 == s4), And(auxSub1 == s7, auxSub2 == s0),
                                       And(auxSub1 == s8, auxSub2 == s1), And(auxSub1 == s8, auxSub2 == s2),
                                       And(auxSub1 == s8, auxSub2 == s3), And(auxSub1 == s9, auxSub2 == s1),
                                       And(auxSub1 == s9, auxSub2 == s2), And(auxSub1 == s10, auxSub2 == s2),
                                       And(auxSub1 == s10, auxSub2 == s6), And(auxSub1 == s10, auxSub2 == s8),
                                       And(auxSub1 == s11, auxSub2 == s4), And(auxSub1 == s11, auxSub2 == s10),
                                       And(auxSub1 == s12, auxSub2 == s0), And(auxSub1 == s12, auxSub2 == s6),
                                       And(auxSub1 == s12, auxSub2 == s7), And(auxSub1 == s12, auxSub2 == s9),
                                       And(auxSub1 == s13, auxSub2 == s0), And(auxSub1 == s13, auxSub2 == s2),
                                       And(auxSub1 == s13, auxSub2 == s4), And(auxSub1 == s13, auxSub2 == s7),
                                       And(auxSub1 == s14, auxSub2 == s0), And(auxSub1 == s14, auxSub2 == s4),
                                       And(auxSub1 == s14, auxSub2 == s11), And(auxSub1 == s14, auxSub2 == s13),
                                       And(auxSub1 == s15, auxSub2 == s1), And(auxSub1 == s15, auxSub2 == s6),
                                       And(auxSub1 == s15, auxSub2 == s12), And(auxSub1 == s15, auxSub2 == s14),
                                       And(auxSub1 == s16, auxSub2 == s7), And(auxSub1 == s16, auxSub2 == s9),
                                       And(auxSub1 == s16, auxSub2 == s11), And(auxSub1 == s16, auxSub2 == s14),
                                       And(auxSub1 == s16, auxSub2 == s15), And(auxSub1 == s17, auxSub2 == s1),
                                       And(auxSub1 == s17, auxSub2 == s7), And(auxSub1 == s17, auxSub2 == s11),
                                       And(auxSub1 == s17, auxSub2 == s16), And(auxSub1 == s18, auxSub2 == s2),
                                       And(auxSub1 == s18, auxSub2 == s3), And(auxSub1 == s18, auxSub2 == s5),
                                       And(auxSub1 == s18, auxSub2 == s6), And(auxSub1 == s18, auxSub2 == s7),
                                       And(auxSub1 == s18, auxSub2 == s17), And(auxSub1 == s19, auxSub2 == s0),
                                       And(auxSub1 == s19, auxSub2 == s1), And(auxSub1 == s19, auxSub2 == s6),
                                       And(auxSub1 == s19, auxSub2 == s13), And(auxSub1 == s19, auxSub2 == s15),
                                       And(auxSub1 == s19, auxSub2 == s16), And(auxSub1 == s19, auxSub2 == s18)),
                                    Sub_Graph(auxSub1, auxSub2) == True, Sub_Graph(auxSub1, auxSub2) == False)))
# Same graph of the Z3, but declared as a python dictionary.
Python_Sub_Graph = {s0: [], s1: [], s2: [s1], s3: [s0, s1], s4: [], s5: [s0], s6: [s4], s7: [s0], s8: [s1, s2, s3],
                    s9: [s1, s2], s10: [s2, s6, s8], s11: [s4, s10], s12: [s0, s6, s7, s9], s13: [s0, s2, s4, s7],
                    s14: [s0, s4, s11, s13], s15: [s1, s6, s12, s14], s16: [s7, s9, s11, s14, s15],
                    s17: [s1, s7, s11, s16], s18: [s2, s3, s5, s6, s7, s17], s19: [s0, s1, s6, s13, s15, s16, s18]}

# Auxiliary graph, used to storage the Subject_Closure_Graph as a python dictionary.
Python_Subject_Closure_Graph = dict()
# Creating the Transitive Closure Graph
set_functions.transitive_closure(Python_Sub_Graph, Python_Subject_Closure_Graph)
# Defining the transitive closure as a Z3 function
Subject_Closure_Graph = Function('Transitive_Closure_Subject_Graph', V_SUB, V_SUB, BoolSort())
#auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)  # Constants to define the ForAll
expressionList1 = []  # List of expressions in the format Subject_Closure_Graph(x, y)
expressionList2 = []  # List of expressions in the format And(x == V_SUB.element, y == V_SUB.element)
for key in Python_Subject_Closure_Graph.keys():
    for node in Python_Subject_Closure_Graph[key]:
        expressionList1.append(Subject_Closure_Graph(key, node))
        expressionList2.append(And(auxSub1 == key, auxSub2 == node))

if expressionList1:  # If the expression list is not empty. The graph is not empty.
    for formula in expressionList1:
        s.add(formula)  # Adding the pairs to the solver
    s.add(ForAll([auxSub1, auxSub2], If(Or(expressionList2),
                                        Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                        # Making the remaining false.
                                        Subject_Closure_Graph(auxSub1, auxSub2) == False)))


Res_Graph = Function('Resources_Graph', V_RES, V_RES, BoolSort())  # Declaring the Resources Graph
# Making the initialisation of the Graph
#auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
s.add(Res_Graph(r2, r1), Res_Graph(r4, r3), Res_Graph(r6, r1), Res_Graph(r6, r2), Res_Graph(r6, r5), Res_Graph(r7, r4),
      Res_Graph(r7, r6), Res_Graph(r8, r1), Res_Graph(r8, r4), Res_Graph(r8, r6), Res_Graph(r9, r0), Res_Graph(r9, r1),
      Res_Graph(r10, r1), Res_Graph(r10, r4), Res_Graph(r10, r6), Res_Graph(r10, r8), Res_Graph(r10, r9),
      Res_Graph(r11, r0), Res_Graph(r11, r5), Res_Graph(r11, r7), Res_Graph(r11, r8), Res_Graph(r12, r0),
      Res_Graph(r12, r1), Res_Graph(r12, r4), Res_Graph(r12, r10), Res_Graph(r12, r11), Res_Graph(r13, r1),
      Res_Graph(r13, r5), Res_Graph(r13, r6), Res_Graph(r13, r8), Res_Graph(r13, r11), Res_Graph(r13, r12),
      Res_Graph(r14, r4), Res_Graph(r14, r5), Res_Graph(r14, r6), Res_Graph(r14, r7), Res_Graph(r14, r10),
      Res_Graph(r15, r5), Res_Graph(r15, r9), Res_Graph(r15, r10), Res_Graph(r15, r12), Res_Graph(r15, r14),
      Res_Graph(r16, r8), Res_Graph(r16, r11), Res_Graph(r16, r14), Res_Graph(r17, r3), Res_Graph(r17, r12),
      Res_Graph(r17, r13), Res_Graph(r17, r16), Res_Graph(r18, r1), Res_Graph(r18, r4), Res_Graph(r18, r5),
      Res_Graph(r18, r10), Res_Graph(r18, r15), Res_Graph(r18, r17), Res_Graph(r19, r1), Res_Graph(r19, r6),
      Res_Graph(r19, r8), Res_Graph(r19, r14), Res_Graph(r19, r15), Res_Graph(r19, r16), Res_Graph(r19, r17),
      Res_Graph(r19, r18))
s.add(ForAll([auxRes1, auxRes2], If(Or(And(auxRes1 == r2, auxRes2 == r1), And(auxRes1 == r4, auxRes2 == r3),
                                       And(auxRes1 == r6, auxRes2 == r1), And(auxRes1 == r6, auxRes2 == r2),
                                       And(auxRes1 == r6, auxRes2 == r5), And(auxRes1 == r7, auxRes2 == r4),
                                       And(auxRes1 == r7, auxRes2 == r6), And(auxRes1 == r8, auxRes2 == r1),
                                       And(auxRes1 == r8, auxRes2 == r4), And(auxRes1 == r8, auxRes2 == r6),
                                       And(auxRes1 == r9, auxRes2 == r0), And(auxRes1 == r9, auxRes2 == r1),
                                       And(auxRes1 == r10, auxRes2 == r1), And(auxRes1 == r10, auxRes2 == r4),
                                       And(auxRes1 == r10, auxRes2 == r6), And(auxRes1 == r10, auxRes2 == r8),
                                       And(auxRes1 == r10, auxRes2 == r9), And(auxRes1 == r11, auxRes2 == r0),
                                       And(auxRes1 == r11, auxRes2 == r5), And(auxRes1 == r11, auxRes2 == r7),
                                       And(auxRes1 == r11, auxRes2 == r8), And(auxRes1 == r12, auxRes2 == r0),
                                       And(auxRes1 == r12, auxRes2 == r1), And(auxRes1 == r12, auxRes2 == r4),
                                       And(auxRes1 == r12, auxRes2 == r10), And(auxRes1 == r12, auxRes2 == r11),
                                       And(auxRes1 == r13, auxRes2 == r1), And(auxRes1 == r13, auxRes2 == r5),
                                       And(auxRes1 == r13, auxRes2 == r6), And(auxRes1 == r13, auxRes2 == r8),
                                       And(auxRes1 == r13, auxRes2 == r11), And(auxRes1 == r13, auxRes2 == r12),
                                       And(auxRes1 == r14, auxRes2 == r4), And(auxRes1 == r14, auxRes2 == r5),
                                       And(auxRes1 == r14, auxRes2 == r6), And(auxRes1 == r14, auxRes2 == r7),
                                       And(auxRes1 == r14, auxRes2 == r10), And(auxRes1 == r15, auxRes2 == r5),
                                       And(auxRes1 == r15, auxRes2 == r9), And(auxRes1 == r15, auxRes2 == r10),
                                       And(auxRes1 == r15, auxRes2 == r12), And(auxRes1 == r15, auxRes2 == r14),
                                       And(auxRes1 == r16, auxRes2 == r8), And(auxRes1 == r16, auxRes2 == r11),
                                       And(auxRes1 == r16, auxRes2 == r14), And(auxRes1 == r17, auxRes2 == r3),
                                       And(auxRes1 == r17, auxRes2 == r12), And(auxRes1 == r17, auxRes2 == r13),
                                       And(auxRes1 == r17, auxRes2 == r16), And(auxRes1 == r18, auxRes2 == r1),
                                       And(auxRes1 == r18, auxRes2 == r4), And(auxRes1 == r18, auxRes2 == r5),
                                       And(auxRes1 == r18, auxRes2 == r10), And(auxRes1 == r18, auxRes2 == r15),
                                       And(auxRes1 == r18, auxRes2 == r17), And(auxRes1 == r19, auxRes2 == r1),
                                       And(auxRes1 == r19, auxRes2 == r6), And(auxRes1 == r19, auxRes2 == r8),
                                       And(auxRes1 == r19, auxRes2 == r14), And(auxRes1 == r19, auxRes2 == r15),
                                       And(auxRes1 == r19, auxRes2 == r16), And(auxRes1 == r19, auxRes2 == r17),
                                       And(auxRes1 == r19, auxRes2 == r18)),
                                    Res_Graph(auxRes1, auxRes2) == True, Res_Graph(auxRes1, auxRes2) == False)))
# Same resource graph of the Z3, but declared as a python dictionary.
Python_Res_Graph = {r0: [], r1: [], r2: [r1], r3: [], r4: [r3], r5: [], r6: [r1, r2, r5], r7: [r4, r6],
                    r8: [r1, r4, r6], r9: [r0, r1], r10: [r1, r4, r6, r8, r9], r11: [r0, r5, r7, r8],
                    r12: [r0, r1, r4, r10, r11], r13: [r1, r5, r6, r8, r11, r12], r14: [r4, r5, r6, r7, r10],
                    r15: [r5, r9, r10, r12, r14], r16: [r8, r11, r14], r17: [r3, r12, r13, r16],
                    r18: [r1, r4, r5, r10, r15, r17], r19: [r1, r6, r8, r14, r15, r16, r17, r18]}

# Auxiliary graph, used to storage the Subject_Closure_Graph as a python dictionary.
Python_Resource_Closure_Graph = dict()
# Creating the Transitive Closure Graph
set_functions.transitive_closure(Python_Res_Graph, Python_Resource_Closure_Graph)
# Defining the transitive closure as a Z3 function
Resource_Closure_Graph = Function('Transitive_Closure_Resources_Graph', V_RES, V_RES, BoolSort())
#auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)  # Constants to define the ForAll
expressionList1 = []  # List of expressions in the format Subject_Closure_Graph(x, y)
expressionList2 = []  # List of expressions in the format And(x == V_SUB.element, y == V_SUB.element)
for key in Python_Resource_Closure_Graph.keys():
    for node in Python_Resource_Closure_Graph[key]:
        expressionList1.append(Resource_Closure_Graph(key, node))
        expressionList2.append(And(auxRes1 == key, auxRes2 == node))

if expressionList1:  # If the expression list is not empty. The graph is not empty.
    for formula in expressionList1:
        s.add(formula)  # Adding the pairs to the solver
    s.add(ForAll([auxRes1, auxRes2], If(Or(expressionList2),
                            Resource_Closure_Graph(auxRes1, auxRes2) == True,
                            Resource_Closure_Graph(auxRes1, auxRes2) == False)))  # Making the remaining false.

predicate = "ForAll([auxSub1, auxSub2], If(Or("
for expression in expressionList2:
    predicate += str(expression)+", "
predicate = predicate[:len(predicate)-2:] + "), Subject_Closure_Graph(auxSub1, auxSub2) == True," \
                                             " Subject_Closure_Graph(auxSub1, auxSub2) == False))"

# Adding the REQUEST_T constant as a z3 relation between (V_SUB-dom(e_sub)) * (V_RES-dom(e_res))
REQUEST_T = Function('REQUEST_T', V_SUB, V_RES, BoolSort())
notDomainSUB = Function('notDomainSub', V_SUB, BoolSort())
notDomainRES = Function('notDomainRes', V_RES, BoolSort())
# Auxiliary variables to the declaration of the predicate of REQUEST_T.
#auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)
# Formulas to describe REQUEST_T
s.add(ForAll(auxSub1, If(Not(Exists(auxSub2, Sub_Graph(auxSub1, auxSub2))),
                         notDomainSUB(auxSub1), notDomainSUB(auxSub1) == False)))
s.add(ForAll(auxRes1, If(Not(Exists(auxRes2, Res_Graph(auxRes1, auxRes2))),
                         notDomainRES(auxRes1), notDomainRES(auxRes1) == False)))
s.add(ForAll([auxSub1, auxRes1], Implies(And(notDomainSUB(auxSub1),
                                             notDomainRES(auxRes1)),
                                         REQUEST_T(auxSub1, auxRes1))))
s.add(Implies(notDomainRES(auxRes1), And(Not(Exists(auxRes2, Res_Graph(auxRes1, auxRes2))
                                             ),
                                         Or(auxRes1 == r0, auxRes1 == r1, auxRes1 == r2, auxRes1 == r3,
                                            auxRes1 == r4, auxRes1 == r5, auxRes1 == r6, auxRes1 == r7,
                                            auxRes1 == r8, auxRes1 == r9, auxRes1 == r10, auxRes1 == r11,
                                            auxRes1 == r12, auxRes1 == r13, auxRes1 == r14, auxRes1 == r15,
                                            auxRes1 == r16, auxRes1 == r17, auxRes1 == r18, auxRes1 == r19)
                                         )
              )
      )
s.add(Implies(notDomainSUB(auxSub1), And(Not(Exists(auxSub2, Sub_Graph(auxSub1, auxSub2))),
                                         Or(auxSub1 == s0, auxSub1 == s1, auxSub1 == s2, auxSub1 == s3, auxSub1 == s4,
                                            auxSub1 == s5, auxSub1 == s6, auxSub1 == s7, auxSub1 == s8, auxSub1 == s9,
                                            auxSub1 == s10, auxSub1 == s11, auxSub1 == s12, auxSub1 == s13,
                                            auxSub1 == s14, auxSub1 == s15, auxSub1 == s16, auxSub1 == s17,
                                            auxSub1 == s18, auxSub1 == s19)
                                         )
              )
      )
s.add(Implies(REQUEST_T(auxSub1, auxRes1), And(notDomainSUB(auxSub1),
                                               notDomainRES(auxRes1))))
# Making REQUEST_T only valid to the described Subjects and Resources
s.add(Not(Exists([auxSub1, auxRes1], Or(And(auxSub1 != s0, auxSub1 != s1, auxSub1 != s2, auxSub1 != s3, auxSub1 != s4,
                                             auxSub1 != s5, auxSub1 != s6, auxSub1 != s7, auxSub1 != s8, auxSub1 != s9,
                                             auxSub1 != s10, auxSub1 != s11, auxSub1 != s12, auxSub1 != s13,
                                             auxSub1 != s14, auxSub1 != s15, auxSub1 != s16, auxSub1 != s17,
                                             auxSub1 != s18, auxSub1 != s19),
                                         And(auxRes1 != r0, auxRes1 != r1, auxRes1 != r2, auxRes1 != r3, auxRes1 != r4,
                                             auxRes1 != r5, auxRes1 != r6, auxRes1 != r7, auxRes1 != r8, auxRes1 != r9,
                                             auxRes1 != r10, auxRes1 != r11, auxRes1 != r12, auxRes1 != r13,
                                             auxRes1 != r14, auxRes1 != r15, auxRes1 != r16, auxRes1 != r17,
                                             auxRes1 != r18, auxRes1 != r19)))))

MODALITY = DeclareSort('ModalityType')  # Creation of modality type.
permission, prohibition = Consts('permission prohibition', MODALITY)  # Creating modality elements.
s.add(Distinct(permission, prohibition))

CONTEXT = DeclareSort('Context')  # Creation of a context.
c0, c1, c2 = Consts('c0 c1 c2', CONTEXT)  # Going to change this later to predicates.
s.add(Distinct(c0, c1, c2))

rules = DeclareSort('rules')  # Creation of a rule type RULE_T in the B machine.
rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38,\
rule39 = Consts('rule30 rule31 rule32 rule33 rule34 rule35 rule36 rule37 rule38 rule39', rules)
s.add(Distinct(rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39))
# Not letting the value of the rules escape
# Auxiliary variables to the declaration of the predicate above.
#auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
s.add(Not(Exists([auxRule1, auxRule2],
                 And(And(auxRule2 != rule30, auxRule2 != rule31, auxRule2 != rule32, auxRule2 != rule33,
                         auxRule2 != rule34, auxRule2 != rule35, auxRule2 != rule36, auxRule2 != rule37,
                         auxRule2 != rule38, auxRule2 != rule39),
                     And(auxRule1 != rule30, auxRule1 != rule31, auxRule1 != rule32, auxRule1 != rule33,
                         auxRule1 != rule34, auxRule1 != rule35, auxRule1 != rule36, auxRule1 != rule37,
                         auxRule1 != rule38, auxRule1 != rule39)))))


# Creation of several graphs as a z3 relation. Used to describe a rule parameters.
rule_subject = Function('rule_subject', rules, V_SUB, BoolSort())
rule_resource = Function('rule_resource', rules, V_RES, BoolSort())
rule_modality = Function('rule_modality', rules, MODALITY, BoolSort())
rule_priority = Function('rule_priority', rules, IntSort(), BoolSort())
rule_condition = Function('rule_condition', rules, CONTEXT, BoolSort())

# Adding the subject for each specific rule.
s.add(rule_subject(rule30, s19), rule_subject(rule31, s7), rule_subject(rule32, s11), rule_subject(rule33, s13),
      rule_subject(rule34, s3), rule_subject(rule35, s7), rule_subject(rule36, s13), rule_subject(rule37, s14),
      rule_subject(rule38, s8), rule_subject(rule39, s0))
#auxRule1 = Const('auxRule1', rules)
#auxSub1 = Const('auxSub1', V_SUB)
s.add(ForAll([auxRule1, auxSub1],
             # If any of this options
             If(Or(And(auxRule1 == rule30, auxSub1 == s19), And(auxRule1 == rule31, auxSub1 == s7),
                   And(auxRule1 == rule32, auxSub1 == s11), And(auxRule1 == rule33, auxSub1 == s13),
                   And(auxRule1 == rule34, auxSub1 == s3), And(auxRule1 == rule35, auxSub1 == s7),
                   And(auxRule1 == rule36, auxSub1 == s13), And(auxRule1 == rule37, auxSub1 == s14),
                   And(auxRule1 == rule38, auxSub1 == s8), And(auxRule1 == rule39, auxSub1 == s0)),
                rule_subject(auxRule1, auxSub1) == True,  # Then True
                rule_subject(auxRule1, auxSub1) == False)))  # Else -> False


# Adding the resource for each specific rule.
s.add(rule_resource(rule30, r17), rule_resource(rule31, r0), rule_resource(rule32, r14), rule_resource(rule33, r6),
      rule_resource(rule34, r8), rule_resource(rule35, r11), rule_resource(rule36, r6), rule_resource(rule37, r4),
      rule_resource(rule38, r15), rule_resource(rule39, r14))
#auxRes1 = Const('auxRes1', V_RES)
s.add(ForAll([auxRule1, auxRes1],
             # If any of this options
             If(Or(And(auxRule1 == rule30, auxRes1 == r17), And(auxRule1 == rule31, auxRes1 == r0),
                   And(auxRule1 == rule32, auxRes1 == r14), And(auxRule1 == rule33, auxRes1 == r6),
                   And(auxRule1 == rule34, auxRes1 == r8), And(auxRule1 == rule35, auxRes1 == r11),
                   And(auxRule1 == rule36, auxRes1 == r6), And(auxRule1 == rule37, auxRes1 == r4),
                   And(auxRule1 == rule38, auxRes1 == r15), And(auxRule1 == rule39, auxRes1 == r14)),
                rule_resource(auxRule1, auxRes1) == True,  # Then True
                rule_resource(auxRule1, auxRes1) == False)))  # Else -> False

# Adding the modality for each specific rule.
s.add(rule_modality(rule30, prohibition), rule_modality(rule31, permission), rule_modality(rule32, permission),
      rule_modality(rule33, permission), rule_modality(rule34, prohibition), rule_modality(rule35, prohibition),
      rule_modality(rule36, permission), rule_modality(rule37, prohibition), rule_modality(rule38, prohibition),
      rule_modality(rule39, permission))
#auxModality = Const('auxModality', MODALITY)
s.add(ForAll([auxRule1, auxModality], If(Or(And(auxRule1 == rule30, auxModality == prohibition),
                                            And(auxRule1 == rule31, auxModality == permission),
                                            And(auxRule1 == rule32, auxModality == permission),
                                            And(auxRule1 == rule33, auxModality == permission),
                                            And(auxRule1 == rule34, auxModality == prohibition),
                                            And(auxRule1 == rule35, auxModality == prohibition),
                                            And(auxRule1 == rule36, auxModality == permission),
                                            And(auxRule1 == rule37, auxModality == prohibition),
                                            And(auxRule1 == rule38, auxModality == prohibition),
                                            And(auxRule1 == rule39, auxModality == permission)),  # If it is this
                                         rule_modality(auxRule1, auxModality) == True,  # Then True
                                         rule_modality(auxRule1, auxModality) == False)))  # Else -> False

# Adding the priority for each specific rule.
s.add(rule_priority(rule30, 1), rule_priority(rule31, 3), rule_priority(rule32, 4), rule_priority(rule33, 1),
      rule_priority(rule34, 3), rule_priority(rule35, 0), rule_priority(rule36, 1), rule_priority(rule37, 1),
      rule_priority(rule38, 0), rule_priority(rule39, 1))
#auxInt = Const('auxInt', IntSort())
s.add(ForAll([auxRule1, auxInt], If(Or(And(auxRule1 == rule30, auxInt == 1), And(auxRule1 == rule31, auxInt == 3),
                                       And(auxRule1 == rule32, auxInt == 4), And(auxRule1 == rule33, auxInt == 1),
                                       And(auxRule1 == rule34, auxInt == 3), And(auxRule1 == rule35, auxInt == 0),
                                       And(auxRule1 == rule36, auxInt == 1), And(auxRule1 == rule37, auxInt == 1),
                                       And(auxRule1 == rule38, auxInt == 0), And(auxRule1 == rule39, auxInt == 1)),
                                    # If it is this
                                    rule_priority(auxRule1, auxInt) == True,  # Then True
                                    rule_priority(auxRule1, auxInt) == False)))  # Else -> False

# Adding the condition for each specific rule.
s.add(rule_condition(rule30, c2), rule_condition(rule30, c0), rule_condition(rule31, c0), rule_condition(rule31, c2),
      rule_condition(rule32, c0), rule_condition(rule33, c1), rule_condition(rule33, c0), rule_condition(rule34, c2),
      rule_condition(rule35, c0), rule_condition(rule35, c2), rule_condition(rule36, c1), rule_condition(rule37, c2),
      rule_condition(rule38, c2), rule_condition(rule38, c0), rule_condition(rule39, c0), rule_condition(rule39, c1))
#auxCon = Const('auxCon', CONTEXT)
s.add(ForAll([auxRule1, auxCon],
             # If any of this options
             If(Or(And(auxRule1 == rule30, auxCon == c2), And(auxRule1 == rule30, auxCon == c0),
                   And(auxRule1 == rule31, auxCon == c0), And(auxRule1 == rule31, auxCon == c2),
                   And(auxRule1 == rule32, auxCon == c0), And(auxRule1 == rule33, auxCon == c1),
                   And(auxRule1 == rule33, auxCon == c0), And(auxRule1 == rule34, auxCon == c2),
                   And(auxRule1 == rule35, auxCon == c0), And(auxRule1 == rule35, auxCon == c2),
                   And(auxRule1 == rule36, auxCon == c1), And(auxRule1 == rule37, auxCon == c2),
                   And(auxRule1 == rule38, auxCon == c2), And(auxRule1 == rule38, auxCon == c0),
                   And(auxRule1 == rule39, auxCon == c0), And(auxRule1 == rule39, auxCon == c1)),
                rule_condition(auxRule1, auxCon) == True,  # Then True
                rule_condition(auxRule1, auxCon) == False)))  # Else -> False

# Adding the lessSpecific constant as a z3 relation between rules.
lessSpecific = Function('lessSpecific', rules, rules, BoolSort())
# Auxiliary variables to the declaration of the predicate of lessSpecific.
#auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
# Auxiliary variables to the declaration of the predicate of lessSpecific.
#auxInt1, auxInt2 = Consts('auxInt1 auxInt2', IntSort())
# Auxiliary variables to the declaration of the predicate of lessSpecific.
#auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)
s.add(Implies(lessSpecific(auxRule1, auxRule2),
              And(rule_priority(auxRule1, auxInt1), rule_priority(auxRule2, auxInt2),
                  rule_subject(auxRule1, auxSub1), rule_subject(auxRule2, auxSub2),
                  auxRule1 != auxRule2,
                  Or(auxInt1 > auxInt2, And(auxInt1 == auxInt2, Subject_Closure_Graph(auxSub1, auxSub2)))
                  )
              )
      )
s.add(ForAll([auxRule1, auxRule2, auxInt1, auxInt2, auxSub1, auxSub2],
             Implies(And(rule_priority(auxRule1, auxInt1), rule_priority(auxRule2, auxInt2),
                         rule_subject(auxRule1, auxSub1), rule_subject(auxRule2, auxSub2),
                         auxRule1 != auxRule2,
                         Or(auxInt1 > auxInt2, And(auxInt1 == auxInt2,
                                                   Subject_Closure_Graph(auxSub1, auxSub2)))),
                     lessSpecific(auxRule1, auxRule2))))  # Formula that fits lessSpecific.

'''
Starting to describe the VARIABLES and INVARIANT clauses from the B machine.
'''
conRule = Function('conRule', CONTEXT, rules, BoolSort())  # Creating of the variable ConRule
#auxCon = Const('auxCon', CONTEXT)
#auxRule1 = Const('auxRule1', rules)
s.add(ForAll([auxCon, auxRule1], Implies(rule_condition(auxRule1, auxCon), conRule(auxCon, auxRule1))))
s.add(Implies(conRule(auxCon, auxRule1), rule_condition(auxRule1, auxCon)))

applicable = Function('applicable', V_SUB, V_RES, rules, BoolSort())  # Declaring VARIABLE applicable
#auxRule1 = Const('auxRule1', rules)
#auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
#auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)
# Defining the applicable variable
s.add(Implies(applicable(auxSub1, auxRes1, auxRule1),
              And(Or(rule_subject(auxRule1, auxSub1),
                     And(Subject_Closure_Graph(auxSub2, auxSub1),
                         rule_subject(auxRule1, auxSub2))
                     ),
                  Or(rule_resource(auxRule1, auxRes1),
                     And(rule_resource(auxRule1, auxRes2),
                         Resource_Closure_Graph(auxRes2, auxRes1))
                     ),
                  REQUEST_T(auxSub1, auxRes1)
                  )
              )
      )
s.add(ForAll([auxRes1, auxSub2, auxRule1, auxRes2, auxSub1], Implies(And(Or(rule_subject(auxRule1, auxSub1),
                                                                           And(rule_subject(auxRule1, auxSub2),
                                                                               Subject_Closure_Graph(auxSub2,
                                                                                                     auxSub1))),
                                                                        Or(rule_resource(auxRule1, auxRes1),
                                                                           And(rule_resource(auxRule1, auxRes2),
                                                                               Resource_Closure_Graph(auxRes2, auxRes1))
                                                                           ),
                                                                        REQUEST_T(auxSub1, auxRes1)
                                                                        ),
                                                                    applicable(auxSub1, auxRes1, auxRule1))
             )
      )

print(s.check())
if s.check() == sat:
    print(s.model()[lessSpecific])
    f = open("model.txt", "w+")
    for variable in s.model():
        f.write(str(variable)), f.write("="), f.write(str(s.model()[variable])), f.write("\n")
    f.close()

    dictOfSubstitutions = dict()
    chosenVariables = [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
                       r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
                       rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39, c0, c1, c2,
                       permission, prohibition]

    # Rewriting the variables
    for variable in chosenVariables:
        with open("model.txt") as f:
            for line in f:
                matches = re.finditer(r""+str(variable)+"=", line)
                for matchNum, match in enumerate(matches):
                    dictOfSubstitutions[variable] = line[match.end():len(line)-1:]
        f.close()
    with open("model.txt", 'r') as f:
        modelContent = f.read()
    f.close()
    for key in dictOfSubstitutions.keys():
        modelContent = re.sub(r""+str(dictOfSubstitutions[key])+"", str(key), modelContent)
    # Erasing the k!#### and replacing for the variables
    modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
    # Erasing k!#### variables
    modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
    # Erasing weird syntax from the solver (If(Var(0) == ...)
    modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "", modelContent)
    modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
    modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
    # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
    modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
    modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
    modelContent = re.sub(r"\[ Or", "[Or", modelContent)
    f = open("model.txt", "w+")
    f.write(modelContent)
    f.close()

    # Rewriting the model for rerun in another Z3 model and accomplish the Exists quantification
    # Adding a new solver
    r = Solver()
    dictOfFormulas = dict()

    formulas = [Sub_Graph, Subject_Closure_Graph, Res_Graph, Resource_Closure_Graph, REQUEST_T, rule_subject,
                rule_resource, rule_modality, rule_priority, rule_condition, lessSpecific, conRule, applicable,
                notDomainSUB, notDomainRES]
    with open("model.txt", 'r') as f:
        modelContent = f.read()

    for formula in formulas:
        if re.search(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE) is not None:
            matches = re.finditer(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE)
            for matchNum, match in enumerate(matches, start=1):
                dictOfFormulas[formula.name()] = modelContent[match.start()+len(formula.name())+2:match.end()-1:]
        else:
            matches = re.finditer(r"%s=\[.*?\n\s*.*?\]" % formula.name(), modelContent, re.MULTILINE | re.DOTALL)
            for matchNum, match in enumerate(matches, start=1):
                dictOfFormulas[formula.name()] = modelContent[match.start()+len(formula.name())+2:match.end()-1:]

    r.add(Distinct(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19))
    r.add(Distinct(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19))
    r.add(Distinct(rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39))
    r.add(Distinct(c0, c1, c2))
    r.add(Distinct(permission, prohibition))
    r.add(Or(auxRule1 == rule30, auxRule1 == rule31, auxRule1 == rule32, auxRule1 == rule33, auxRule1 == rule34,
             auxRule1 == rule35, auxRule1 == rule36, auxRule1 == rule37, auxRule1 == rule38, auxRule1 == rule39))
    r.add(Or(auxRule2 == rule30, auxRule2 == rule31, auxRule2 == rule32, auxRule2 == rule33, auxRule2 == rule34,
             auxRule2 == rule35, auxRule2 == rule36, auxRule2 == rule37, auxRule2 == rule38, auxRule2 == rule39))
    for formula in dictOfFormulas.keys():
        if formula == 'Subject_Graph':
            predicate = eval(
                dictOfFormulas['Subject_Graph'].replace(', s', ', auxSub2 == s').replace('And(s', 'And(auxSub1 == s'))
            r.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                Sub_Graph(auxSub1, auxSub2) == True,
                                                Sub_Graph(auxSub1, auxSub2) == False)
                         )
                  )
        if formula == 'Resources_Graph':
            predicate = eval(
                dictOfFormulas['Resources_Graph'].replace(', r', ', auxRes2 == r').replace('And(r', 'And(auxRes1 == r'))
            r.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                Res_Graph(auxRes1, auxRes2) == True,
                                                Res_Graph(auxRes1, auxRes2) == False)
                         )
                  )
        if formula == 'Transitive_Closure_Subject_Graph':
            predicate = eval(
                dictOfFormulas['Transitive_Closure_Subject_Graph'].replace(', s', ', auxSub2 == s').replace('And(s', 'And(auxSub1 == s'))
            r.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                                Subject_Closure_Graph(auxSub1, auxSub2) == False)
                         )
                  )
        if formula == 'Transitive_Closure_Resources_Graph':
            predicate = eval(
                dictOfFormulas['Transitive_Closure_Resources_Graph'].replace(', r', ', auxRes2 == r').replace('And(r', 'And(auxRes1 == r'))
            r.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                Resource_Closure_Graph(auxRes1, auxRes2) == True,
                                                Resource_Closure_Graph(auxRes1, auxRes2) == False)
                         )
                  )
        if formula == 'REQUEST_T':
            predicate = eval(
                dictOfFormulas['REQUEST_T'].replace(', r', ', auxRes1 == r').replace('And(s', 'And(auxSub1 == s'))
            r.add(ForAll([auxSub1, auxRes1], If(predicate,
                                                REQUEST_T(auxSub1, auxRes1) == True,
                                                REQUEST_T(auxSub1, auxRes1) == False)))

        if formula == 'rule_modality':
            predicate = eval(
                dictOfFormulas['rule_modality'].replace('Not(p', 'Not(auxModality == p').replace(
                    'Not(rule', 'Not(auxRule1 == rule'))
            r.add(ForAll([auxRule1, auxModality], If(predicate,  # If it is this
                                                     rule_modality(auxRule1, auxModality) == True,  # Then True
                                                     rule_modality(auxRule1, auxModality) == False)))  # Else -> False)

        if formula == 'rule_subject':
            predicate = eval(
                dictOfFormulas['rule_subject'].replace(', s', ', auxSub1 == s').replace(
                    'And(rule', 'And(auxRule1 == rule'))
            r.add(ForAll([auxRule1, auxSub1], If(predicate,  # If it is this
                                                 rule_subject(auxRule1, auxSub1) == True,  # Then True
                                                 rule_subject(auxRule1, auxSub1) == False)))  # Else -> False)

        if formula == 'rule_resource':
            predicate = eval(
                dictOfFormulas['rule_resource'].replace(', r', ', auxRes1 == r').replace(
                    'And(rule', 'And(auxRule1 == rule'))
            r.add(ForAll([auxRule1, auxRes1], If(predicate,  # If it is this
                                                 rule_resource(auxRule1, auxRes1) == True,  # Then True
                                                 rule_resource(auxRule1, auxRes1) == False)))  # Else -> False)

        if formula == 'rule_condition':
            predicate = eval(dictOfFormulas['rule_condition'].replace(
                ', c', ', auxCon == c').replace('And(rule', 'And(auxRule1 == rule'))
            r.add(ForAll([auxRule1, auxCon], If(predicate,  # If it is this
                                                rule_condition(auxRule1, auxCon) == True,  # Then True
                                                rule_condition(auxRule1, auxCon) == False)))  # Else -> False))

        if formula == 'rule_priority':
            predicate = eval(dictOfFormulas['rule_priority'].replace(', 4', ', auxInt == 4').replace(
                ', 2', ', auxInt == 2').replace(', 3', ', auxInt == 3').replace(', 0', ', auxInt == 0').replace(
                ', 1', ', auxInt == 1').replace('And(rule', 'And(auxRule1 == rule'))
            r.add(ForAll([auxRule1, auxInt], If(predicate,  # If it is this
                                                rule_priority(auxRule1, auxInt) == True,  # Then True
                                                rule_priority(auxRule1, auxInt) == False)))  # Else -> False))

        if formula == 'lessSpecific':
            predicate = eval(dictOfFormulas['lessSpecific'].replace(', r', ', auxRule2 == r').replace(
                'And(r', 'And(auxRule1 == r'))
            r.add(ForAll([auxRule1, auxRule2], If(predicate,
                                                  lessSpecific(auxRule1, auxRule2),
                                                  Not(lessSpecific(auxRule1, auxRule2)))))

        if formula == 'conRule':
            predicate = eval(dictOfFormulas['conRule'].replace(', r', ', auxRule1 == r').replace(
                'And(c', 'And(auxCon == c'))
            r.add(ForAll([auxRule1, auxCon], If(predicate,
                                                conRule(auxCon, auxRule1),
                                                Not(conRule(auxCon, auxRule1)))))

        if formula == 'applicable':
            predicate = eval(dictOfFormulas['applicable'].replace(
                ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s', 'And(auxSub1 == s'))
            r.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                          applicable(auxSub1, auxRes1, auxRule1),
                                                          Not(applicable(auxSub1, auxRes1, auxRule1)))))

        if formula == 'notDomainSub':
            predicate = eval(dictOfFormulas['notDomainSub'].replace('(s', '(auxSub1 == s').replace(', s',
                                                                                                   ', auxSub1 == s'))
            r.add(ForAll([auxSub1], If(predicate,
                                       notDomainSUB(auxSub1),
                                       Not(notDomainSUB(auxSub1)))))

        if formula == 'notDomainRes':
            predicate = eval(dictOfFormulas['notDomainRes'].replace('(r', '(auxRes1 == r').replace(', r',
                                                                                                   ', auxRes1 == r'))
            r.add(ForAll([auxRes1], If(predicate,
                                       notDomainRES(auxRes1),
                                       Not(notDomainRES(auxRes1)))))

        maxElem = Function('maxElem', V_SUB, V_RES, rules, BoolSort())
        #auxRes1 = Const('auxRes1', V_RES)
        #auxSub1 = Const('auxSub1', V_SUB)
        #auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
        r.add(ForAll([auxSub1, auxRes1, auxRule1], If(And(applicable(auxSub1, auxRes1, auxRule1),
                                                          Not(Exists(auxRule2,
                                                                     And(applicable(auxSub1, auxRes1, auxRule2),
                                                                         lessSpecific(auxRule1, auxRule2))))),
                                                      maxElem(auxSub1, auxRes1, auxRule1),
                                                      Not(maxElem(auxSub1, auxRes1, auxRule1)))))

    print(r.check())
    if r.check() == sat:
        # print(r.model()[isPrecededBy])
        f = open("model2.txt", "w+")
        for variable in r.model():
            f.write(str(variable)), f.write("="), f.write(str(r.model()[variable])), f.write("\n")
        f.close()

        dictOfSubstitutions = dict()
        chosenVariables = [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
                           r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
                           rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39, c0, c1, c2,
                           permission, prohibition]

        # Rewriting the variables
        for variable in chosenVariables:
            with open("model2.txt") as f:
                for line in f:
                    matches = re.finditer(r"" + str(variable) + "=", line)
                    for matchNum, match in enumerate(matches):
                        dictOfSubstitutions[variable] = line[match.end():len(line) - 1:]
            f.close()

        with open("model2.txt", 'r') as f:
            modelContent = f.read()
        f.close()
        for key in dictOfSubstitutions.keys():
            modelContent = re.sub(r"\b%s\b" % dictOfSubstitutions[key], str(key), modelContent, 0, re.MULTILINE)
        # Erasing the k!#### and replacing for the variables
        modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
        # Erasing k!#### variables
        modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
        # Erasing weird syntax from the solver (If(Var(0) == ...)
        modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "",
                              modelContent)
        modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
        modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
        # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
        modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
        modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
        modelContent = re.sub(r"\[ Or", "[Or", modelContent)
        f = open("model2.txt", "w+")
        f.write(modelContent)
        f.close()

        # Rewriting the model for rerun in another Z3 model and accomplish the Exists quantification
        # Adding a new solver
        q = Solver()
        dictOfFormulas = dict()

        formulas = [Sub_Graph, Subject_Closure_Graph, Res_Graph, Resource_Closure_Graph, REQUEST_T, rule_subject,
                    rule_resource, rule_modality, rule_priority, rule_condition, lessSpecific, conRule, applicable,
                    notDomainSUB, notDomainRES, maxElem]
        with open("model2.txt", 'r') as f:
            modelContent = f.read()

        for formula in formulas:
            if re.search(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE) is not None:
                matches = re.finditer(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE)
                for matchNum, match in enumerate(matches, start=1):
                    dictOfFormulas[formula.name()] = modelContent[
                                                     match.start() + len(formula.name()) + 2:match.end() - 1:]
            else:
                matches = re.finditer(r"%s=\[.*?\n\s*.*?\]" % formula.name(), modelContent, re.MULTILINE | re.DOTALL)
                for matchNum, match in enumerate(matches, start=1):
                    dictOfFormulas[formula.name()] = modelContent[
                                                     match.start() + len(formula.name()) + 2:match.end() - 1:]

        q.add(Distinct(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19))
        q.add(Distinct(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19))
        q.add(Distinct(rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39))
        q.add(Distinct(c0, c1, c2))
        q.add(Distinct(permission, prohibition))
        q.add(Or(auxRule1 == rule30, auxRule1 == rule31, auxRule1 == rule32, auxRule1 == rule33, auxRule1 == rule34,
                 auxRule1 == rule35, auxRule1 == rule36, auxRule1 == rule37, auxRule1 == rule38, auxRule1 == rule39))
        q.add(Or(auxRule2 == rule30, auxRule2 == rule31, auxRule2 == rule32, auxRule2 == rule33, auxRule2 == rule34,
                 auxRule2 == rule35, auxRule2 == rule36, auxRule2 == rule37, auxRule2 == rule38, auxRule2 == rule39))
        for formula in dictOfFormulas.keys():
            if formula == 'Subject_Graph':
                predicate = eval(
                    dictOfFormulas['Subject_Graph'].replace('(Not(s', '(Not(auxSub1 == s').replace(', Not(s',
                                                                                                   ', Not(auxSub2 == s')
                )
                q.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                    Sub_Graph(auxSub1, auxSub2) == True,
                                                    Sub_Graph(auxSub1, auxSub2) == False)
                             )
                      )
            if formula == 'Resources_Graph':
                predicate = eval(
                    dictOfFormulas['Resources_Graph'].replace('(Not(r',
                                                              '(Not(auxRes1 == r').replace(', Not(r',
                                                                                           ', Not(auxRes2 == r'))
                q.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                    Res_Graph(auxRes1, auxRes2) == True,
                                                    Res_Graph(auxRes1, auxRes2) == False)
                             )
                      )
            if formula == 'Transitive_Closure_Subject_Graph':
                predicate = eval(
                    dictOfFormulas['Transitive_Closure_Subject_Graph'].replace('(Not(s',
                                                                               '(Not(auxSub1 == s').replace(', Not(s',
                                                                                                            ', Not(auxSub2 == s')
                )
                q.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                    Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                                    Subject_Closure_Graph(auxSub1, auxSub2) == False)
                             )
                      )
            if formula == 'Transitive_Closure_Resources_Graph':
                predicate = eval(
                    dictOfFormulas['Transitive_Closure_Resources_Graph'].replace('(Not(r',
                                                                                 '(Not(auxRes1 == r').replace(', Not(r',
                                                                                                              ', Not(auxRes2 == r'))
                q.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                    Resource_Closure_Graph(auxRes1, auxRes2) == True,
                                                    Resource_Closure_Graph(auxRes1, auxRes2) == False)
                             )
                      )
            if formula == 'REQUEST_T':
                predicate = eval(
                    dictOfFormulas['REQUEST_T'].replace(', Not(r', ', Not(auxRes1 == r').replace('Not(s', 'Not(auxSub1 == s'))
                q.add(ForAll([auxSub1, auxRes1], If(predicate,
                                                    REQUEST_T(auxSub1, auxRes1) == True,
                                                    REQUEST_T(auxSub1, auxRes1) == False)))

            if formula == 'rule_modality':
                predicate = eval(
                    dictOfFormulas['rule_modality'].replace('Not(p', 'Not(auxModality == p').replace(
                        'Not(rule', 'Not(auxRule1 == rule'))
                q.add(ForAll([auxRule1, auxModality], If(predicate,  # If it is this
                                                         rule_modality(auxRule1, auxModality) == True,  # Then True
                                                         rule_modality(auxRule1,
                                                                       auxModality) == False)))  # Else -> False)

            if formula == 'rule_subject':
                predicate = eval(
                    dictOfFormulas['rule_subject'].replace(', Not(s', ', Not(auxSub1 == s').replace(
                        'Not(rule', 'Not(auxRule1 == rule'))
                q.add(ForAll([auxRule1, auxSub1], If(predicate,  # If it is this
                                                     rule_subject(auxRule1, auxSub1) == True,  # Then True
                                                     rule_subject(auxRule1, auxSub1) == False)))  # Else -> False)

            if formula == 'rule_resource':
                predicate = eval(
                    dictOfFormulas['rule_resource'].replace(', Not(r', ', Not(auxRes1 == r').replace(
                        'Not(rule', 'Not(auxRule1 == rule'))
                q.add(ForAll([auxRule1, auxRes1], If(predicate,  # If it is this
                                                     rule_resource(auxRule1, auxRes1) == True,  # Then True
                                                     rule_resource(auxRule1, auxRes1) == False)))  # Else -> False)

            if formula == 'rule_condition':
                predicate = eval(dictOfFormulas['rule_condition'].replace(
                    ', Not(c', ', Not(auxCon == c').replace('Not(rule', 'Not(auxRule1 == rule'))
                q.add(ForAll([auxRule1, auxCon], If(predicate,  # If it is this
                                                    rule_condition(auxRule1, auxCon) == True,  # Then True
                                                    rule_condition(auxRule1, auxCon) == False)))  # Else -> False))

            if formula == 'rule_priority':
                predicate = eval(dictOfFormulas['rule_priority'].replace(', Not(4', ', Not(auxInt == 4').replace(
                    ', Not(2', ', Not(auxInt == 2').replace(
                    ', Not(3', ', Not(auxInt == 3').replace(
                    ', Not(0', ', Not(auxInt == 0').replace(
                    ', Not(1', ', Not(auxInt == 1').replace('Not(rule', 'Not(auxRule1 == rule'))
                q.add(ForAll([auxRule1, auxInt], If(predicate,  # If it is this
                                                    rule_priority(auxRule1, auxInt) == True,  # Then True
                                                    rule_priority(auxRule1, auxInt) == False)))  # Else -> False))

            if formula == 'lessSpecific':
                predicate = eval(dictOfFormulas['lessSpecific'].replace(', r', ', auxRule2 == r').replace(
                    'And(r', 'And(auxRule1 == r'))
                q.add(ForAll([auxRule1, auxRule2], If(predicate,
                                                      lessSpecific(auxRule1, auxRule2),
                                                      Not(lessSpecific(auxRule1, auxRule2)))))

            if formula == 'conRule':
                predicate = eval(dictOfFormulas['conRule'].replace(', Not(r', ', Not(auxRule1 == r').replace(
                    'Not(c', 'Not(auxCon == c'))
                q.add(ForAll([auxRule1, auxCon], If(predicate,
                                                    conRule(auxCon, auxRule1),
                                                    Not(conRule(auxCon, auxRule1)))))

            if formula == 'applicable':
                predicate = eval(dictOfFormulas['applicable'].replace(
                    ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                             'And(auxSub1 == s'))
                q.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                              applicable(auxSub1, auxRes1, auxRule1),
                                                              Not(applicable(auxSub1, auxRes1, auxRule1)))))

            if formula == 'notDomainSub':
                predicate = eval(dictOfFormulas['notDomainSub'].replace('(s', '(auxSub1 == s').replace(', s',
                                                                                                       ', auxSub1 == s'))
                q.add(ForAll([auxSub1], If(predicate,
                                           notDomainSUB(auxSub1),
                                           Not(notDomainSUB(auxSub1)))))

            if formula == 'notDomainRes':
                predicate = eval(dictOfFormulas['notDomainRes'].replace('(r', '(auxRes1 == r').replace(', r',
                                                                                                       ', auxRes1 == r'))
                q.add(ForAll([auxRes1], If(predicate,
                                           notDomainRES(auxRes1),
                                           Not(notDomainRES(auxRes1)))))

            if formula == 'maxElem':
                predicate = eval(dictOfFormulas['maxElem'].replace(
                    ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                             'And(auxSub1 == s'))
                q.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                              maxElem(auxSub1, auxRes1, auxRule1),
                                                              Not(maxElem(auxSub1, auxRes1, auxRule1)))))

            isPrecededBy = Function('isPrecededBy', V_SUB, V_RES, rules, rules, BoolSort())
            #auxRule1, auxRule2, auxRule3 = Consts('auxRule1 auxRule2 auxRule3', rules)
            #auxRes1 = Const('auxRes1', V_RES)
            #auxSub1 = Const('auxSub1', V_SUB)
            q.add(ForAll([auxSub1, auxRes1, auxRule1, auxRule2],
                         Implies(And(REQUEST_T(auxSub1, auxRes1),
                                     applicable(auxSub1, auxRes1, auxRule1),
                                     applicable(auxSub1, auxRes1, auxRule2),
                                     auxRule1 != auxRule2,
                                     Or(lessSpecific(auxRule1, auxRule2),
                                        And(maxElem(auxSub1, auxRes1, auxRule1),
                                            maxElem(auxSub1, auxRes1, auxRule2),
                                            rule_modality(auxRule1, permission),
                                            rule_modality(auxRule2, prohibition)
                                            )
                                        )
                                     ),
                                 isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2)
                                 )
                         )
                  )
            q.add(Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                          And(REQUEST_T(auxSub1, auxRes1),
                              applicable(auxSub1, auxRes1, auxRule1),
                              applicable(auxSub1, auxRes1, auxRule2),
                              auxRule1 != auxRule2,
                              Or(lessSpecific(auxRule1, auxRule2),
                                 And(maxElem(auxSub1, auxRes1, auxRule1),
                                     maxElem(auxSub1, auxRes1, auxRule2),
                                     rule_modality(auxRule1, permission),
                                     rule_modality(auxRule2, prohibition)
                                     )
                                 )
                              )
                          )
                  )


        print(q.check())
        if q.check() == sat:
            f = open("model3.txt", "w+")
            for variable in q.model():
                f.write(str(variable)), f.write("="), f.write(str(q.model()[variable])), f.write("\n")
            f.close()

            dictOfSubstitutions = dict()
            chosenVariables = [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18,
                               s19,
                               r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
                               r19,
                               rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39, c0,
                               c1, c2,
                               permission, prohibition]

            # Rewriting the variables
            for variable in chosenVariables:
                with open("model3.txt") as f:
                    for line in f:
                        matches = re.finditer(r"" + str(variable) + "=", line)
                        for matchNum, match in enumerate(matches):
                            dictOfSubstitutions[variable] = line[match.end():len(line) - 1:]
                f.close()

            with open("model3.txt", 'r') as f:
                modelContent = f.read()
            f.close()
            for key in dictOfSubstitutions.keys():
                modelContent = re.sub(r"\b%s\b" % dictOfSubstitutions[key], str(key), modelContent, 0, re.MULTILINE)
            # Erasing the k!#### and replacing for the variables
            modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
            # Erasing k!#### variables
            modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
            # Erasing weird syntax from the solver (If(Var(0) == ...)
            modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "",
                                  modelContent)
            modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
            modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
            # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
            modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
            modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
            modelContent = re.sub(r"\[ Or", "[Or", modelContent)
            f = open("model3.txt", "w+")
            f.write(modelContent)
            f.close()

            # Rewriting the model for rerun in another Z3 model and accomplish the Exists quantification
            # Adding a new solver
            u = Solver()
            dictOfFormulas = dict()

            formulas = [Sub_Graph, Subject_Closure_Graph, Res_Graph, Resource_Closure_Graph, REQUEST_T,
                        rule_subject,
                        rule_resource, rule_modality, rule_priority, rule_condition, lessSpecific, conRule,
                        applicable,
                        notDomainSUB, notDomainRES, maxElem, isPrecededBy]
            with open("model3.txt", 'r') as f:
                modelContent = f.read()

            for formula in formulas:
                if re.search(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE) is not None:
                    matches = re.finditer(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE)
                    for matchNum, match in enumerate(matches, start=1):
                        dictOfFormulas[formula.name()] = modelContent[
                                                         match.start() + len(formula.name()) + 2:match.end() - 1:]
                else:
                    matches = re.finditer(r"%s=\[.*?\n\s*.*?\]" % formula.name(), modelContent,
                                          re.MULTILINE | re.DOTALL)
                    for matchNum, match in enumerate(matches, start=1):
                        dictOfFormulas[formula.name()] = modelContent[
                                                         match.start() + len(formula.name()) + 2:match.end() - 1:]

            u.add(
                Distinct(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19))
            u.add(
                Distinct(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19))
            u.add(Distinct(rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39))
            u.add(Distinct(c0, c1, c2))
            u.add(Distinct(permission, prohibition))
            u.add(Or(auxRule1 == rule30, auxRule1 == rule31, auxRule1 == rule32, auxRule1 == rule33,
                     auxRule1 == rule34,
                     auxRule1 == rule35, auxRule1 == rule36, auxRule1 == rule37, auxRule1 == rule38,
                     auxRule1 == rule39))
            u.add(Or(auxRule2 == rule30, auxRule2 == rule31, auxRule2 == rule32, auxRule2 == rule33,
                     auxRule2 == rule34,
                     auxRule2 == rule35, auxRule2 == rule36, auxRule2 == rule37, auxRule2 == rule38,
                     auxRule2 == rule39))
            for formula in dictOfFormulas.keys():
                if formula == 'Subject_Graph':
                    predicate = eval(
                        dictOfFormulas['Subject_Graph'].replace('(Not(s', '(Not(auxSub1 == s').replace(', Not(s',
                                                                                                       ', Not(auxSub2 == s')
                    )
                    u.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                        Sub_Graph(auxSub1, auxSub2) == True,
                                                        Sub_Graph(auxSub1, auxSub2) == False)
                                 )
                          )
                if formula == 'Resources_Graph':
                    predicate = eval(
                        dictOfFormulas['Resources_Graph'].replace('(Not(r',
                                                                  '(Not(auxRes1 == r').replace(', Not(r',
                                                                                               ', Not(auxRes2 == r'))
                    u.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                        Res_Graph(auxRes1, auxRes2) == True,
                                                        Res_Graph(auxRes1, auxRes2) == False)
                                 )
                          )
                if formula == 'Transitive_Closure_Subject_Graph':
                    predicate = eval(
                        dictOfFormulas['Transitive_Closure_Subject_Graph'].replace('(Not(s',
                                                                                   '(Not(auxSub1 == s').replace(
                            ', Not(s',
                            ', Not(auxSub2 == s')
                    )
                    u.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                        Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                                        Subject_Closure_Graph(auxSub1, auxSub2) == False)
                                 )
                          )
                if formula == 'Transitive_Closure_Resources_Graph':
                    predicate = eval(
                        dictOfFormulas['Transitive_Closure_Resources_Graph'].replace('(Not(r',
                                                                                     '(Not(auxRes1 == r').replace(
                            ', Not(r',
                            ', Not(auxRes2 == r'))
                    u.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                        Resource_Closure_Graph(auxRes1, auxRes2) == True,
                                                        Resource_Closure_Graph(auxRes1, auxRes2) == False)
                                 )
                          )
                if formula == 'REQUEST_T':
                    predicate = eval(
                        dictOfFormulas['REQUEST_T'].replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                             'And(auxSub1 == s'))
                    u.add(ForAll([auxSub1, auxRes1], If(predicate,
                                                        REQUEST_T(auxSub1, auxRes1) == True,
                                                        REQUEST_T(auxSub1, auxRes1) == False)))

                if formula == 'rule_modality':
                    predicate = eval(
                        dictOfFormulas['rule_modality'].replace(', p', ', auxModality == p').replace(
                            'And(rule', 'And(auxRule1 == rule'))
                    u.add(ForAll([auxRule1, auxModality], If(predicate,  # If it is this
                                                             rule_modality(auxRule1, auxModality) == True,
                                                             # Then True
                                                             rule_modality(auxRule1,
                                                                           auxModality) == False)))  # Else -> False)

                if formula == 'rule_subject':
                    predicate = eval(
                        dictOfFormulas['rule_subject'].replace(', Not(s', ', Not(auxSub1 == s').replace(
                            'Not(rule', 'Not(auxRule1 == rule'))
                    u.add(ForAll([auxRule1, auxSub1], If(predicate,  # If it is this
                                                         rule_subject(auxRule1, auxSub1) == True,  # Then True
                                                         rule_subject(auxRule1,
                                                                      auxSub1) == False)))  # Else -> False)

                if formula == 'rule_resource':
                    predicate = eval(
                        dictOfFormulas['rule_resource'].replace(', Not(r', ', Not(auxRes1 == r').replace(
                            'Not(rule', 'Not(auxRule1 == rule'))
                    u.add(ForAll([auxRule1, auxRes1], If(predicate,  # If it is this
                                                         rule_resource(auxRule1, auxRes1) == True,  # Then True
                                                         rule_resource(auxRule1,
                                                                       auxRes1) == False)))  # Else -> False)

                if formula == 'rule_condition':
                    predicate = eval(dictOfFormulas['rule_condition'].replace(
                        ', Not(c', ', Not(auxCon == c').replace('Not(rule', 'Not(auxRule1 == rule'))
                    u.add(ForAll([auxRule1, auxCon], If(predicate,  # If it is this
                                                        rule_condition(auxRule1, auxCon) == True,  # Then True
                                                        rule_condition(auxRule1,
                                                                       auxCon) == False)))  # Else -> False))

                if formula == 'rule_priority':
                    predicate = eval(
                        dictOfFormulas['rule_priority'].replace(', Not(4', ', Not(auxInt == 4').replace(
                            ', Not(2', ', Not(auxInt == 2').replace(
                            ', Not(3', ', Not(auxInt == 3').replace(
                            ', Not(0', ', Not(auxInt == 0').replace(
                            ', Not(1', ', Not(auxInt == 1').replace('Not(rule', 'Not(auxRule1 == rule'))
                    u.add(ForAll([auxRule1, auxInt], If(predicate,  # If it is this
                                                        rule_priority(auxRule1, auxInt) == True,  # Then True
                                                        rule_priority(auxRule1,
                                                                      auxInt) == False)))  # Else -> False))

                if formula == 'lessSpecific':
                    predicate = eval(dictOfFormulas['lessSpecific'].replace(', r', ', auxRule2 == r').replace(
                        'And(r', 'And(auxRule1 == r'))
                    u.add(ForAll([auxRule1, auxRule2], If(predicate,
                                                          lessSpecific(auxRule1, auxRule2),
                                                          Not(lessSpecific(auxRule1, auxRule2)))))

                if formula == 'conRule':
                    predicate = eval(dictOfFormulas['conRule'].replace(', Not(r', ', Not(auxRule1 == r').replace(
                        '(Not(c', '(Not(auxCon == c'))
                    u.add(ForAll([auxRule1, auxCon], If(predicate,
                                                        conRule(auxCon, auxRule1),
                                                        Not(conRule(auxCon, auxRule1)))))

                if formula == 'applicable':
                    predicate = eval(dictOfFormulas['applicable'].replace(
                        ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                                 'And(auxSub1 == s'))
                    u.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                  applicable(auxSub1, auxRes1, auxRule1),
                                                                  Not(applicable(auxSub1, auxRes1, auxRule1)))))

                if formula == 'notDomainSub':
                    predicate = eval(dictOfFormulas['notDomainSub'].replace('(s', '(auxSub1 == s').replace(', s',
                                                                                                           ', auxSub1 == s'))
                    u.add(ForAll([auxSub1], If(predicate,
                                               notDomainSUB(auxSub1),
                                               Not(notDomainSUB(auxSub1)))))

                if formula == 'notDomainRes':
                    predicate = eval(dictOfFormulas['notDomainRes'].replace('(r', '(auxRes1 == r').replace(', r',
                                                                                                           ', auxRes1 == r'))
                    u.add(ForAll([auxRes1], If(predicate,
                                               notDomainRES(auxRes1),
                                               Not(notDomainRES(auxRes1)))))

                if formula == 'maxElem':
                    predicate = eval(dictOfFormulas['maxElem'].replace(
                        ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                                 'And(auxSub1 == s'))
                    u.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                  maxElem(auxSub1, auxRes1, auxRule1),
                                                                  Not(maxElem(auxSub1, auxRes1, auxRule1)))))

                if formula == 'isPrecededBy':
                    dictOfFormulas['isPrecededBy'] = dictOfFormulas['isPrecededBy'].replace(', rule', ', auxRule1 == rule').replace(
                        'And(s', 'And(auxSub1 == s').replace(', r', ', auxRes1 == r')
                    matches = re.finditer(r"auxRule1", dictOfFormulas['isPrecededBy'], re.MULTILINE)

                    for matchNum, match in enumerate(matches, start=1):
                        if matchNum % 2 == 0:
                            dictOfFormulas['isPrecededBy'] = list(dictOfFormulas['isPrecededBy'])
                            dictOfFormulas['isPrecededBy'][match.end()-1] = '2'
                            dictOfFormulas['isPrecededBy'] = "".join(dictOfFormulas['isPrecededBy'])

                    predicate = eval(dictOfFormulas['isPrecededBy'])
                    u.add(ForAll([auxSub1, auxRes1, auxRule1, auxRule2],
                                 If(predicate,
                                    isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                                    Not(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2)))))

                pseudoSink = Function('pseudoSink', V_SUB, V_RES, CONTEXT, rules, BoolSort())
                #auxRes1 = Const('auxRes1', V_RES)
                #auxSub1 = Const('auxSub1', V_SUB)
                #auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
                #auxCon = Const('auxCon', CONTEXT)
                u.add(ForAll([auxSub1, auxRes1, auxCon, auxRule1],
                             If(And(applicable(auxSub1, auxRes1, auxRule1),
                                    conRule(auxCon, auxRule1),
                                    ForAll([auxRule2],
                                           Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                                                   Not(conRule(auxCon, auxRule2))))),
                                pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                Not(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1))
                                )
                             )
                      )
                u.add(Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                              And(applicable(auxSub1, auxRes1, auxRule1),
                                  conRule(auxCon, auxRule1),
                                  ForAll([auxRule2],
                                         Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                                                 Not(conRule(auxCon, auxRule2)))))
                              )
                      )

            print(u.check())
            if u.check() == sat:
                f = open("model4.txt", "w+")
                for variable in u.model():
                    f.write(str(variable)), f.write("="), f.write(str(u.model()[variable])), f.write("\n")
                f.close()

                dictOfSubstitutions = dict()
                chosenVariables = [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18,
                                   s19,
                                   r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
                                   r19,
                                   rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39, c0,
                                   c1, c2,
                                   permission, prohibition]

                # Rewriting the variables
                for variable in chosenVariables:
                    with open("model4.txt") as f:
                        for line in f:
                            matches = re.finditer(r"" + str(variable) + "=", line)
                            for matchNum, match in enumerate(matches):
                                dictOfSubstitutions[variable] = line[match.end():len(line) - 1:]
                    f.close()

                with open("model4.txt", 'r') as f:
                    modelContent = f.read()
                f.close()
                for key in dictOfSubstitutions.keys():
                    modelContent = re.sub(r"\b%s\b" % dictOfSubstitutions[key], str(key), modelContent, 0, re.MULTILINE)
                # Erasing the k!#### and replacing for the variables
                modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
                # Erasing k!#### variables
                modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
                # Erasing weird syntax from the solver (If(Var(0) == ...)
                modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "",
                                      modelContent)
                modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
                modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
                # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
                modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
                modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
                modelContent = re.sub(r"\[ Or", "[Or", modelContent)
                f = open("model4.txt", "w+")
                f.write(modelContent)
                f.close()

                # Rewriting the model for rerun in another Z3 model and accomplish the Exists quantification
                # Adding a new solver
                v = Solver()
                dictOfFormulas = dict()

                formulas = [Sub_Graph, Subject_Closure_Graph, Res_Graph, Resource_Closure_Graph, REQUEST_T,
                            rule_subject,
                            rule_resource, rule_modality, rule_priority, rule_condition, lessSpecific, conRule,
                            applicable,
                            notDomainSUB, notDomainRES, maxElem, isPrecededBy, pseudoSink]
                with open("model4.txt", 'r') as f:
                    modelContent = f.read()

                for formula in formulas:
                    if re.search(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE) is not None:
                        matches = re.finditer(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE)
                        for matchNum, match in enumerate(matches, start=1):
                            dictOfFormulas[formula.name()] = modelContent[
                                                             match.start() + len(formula.name()) + 2:match.end() - 1:]
                    else:
                        matches = re.finditer(r"%s=\[.*?\n\s*.*?\]" % formula.name(), modelContent,
                                              re.MULTILINE | re.DOTALL)
                        for matchNum, match in enumerate(matches, start=1):
                            dictOfFormulas[formula.name()] = modelContent[
                                                             match.start() + len(formula.name()) + 2:match.end() - 1:]

                v.add(
                    Distinct(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19))
                v.add(
                    Distinct(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19))
                v.add(Distinct(rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39))
                v.add(Distinct(c0, c1, c2))
                v.add(Distinct(permission, prohibition))
                v.add(Or(auxRule1 == rule30, auxRule1 == rule31, auxRule1 == rule32, auxRule1 == rule33,
                         auxRule1 == rule34,
                         auxRule1 == rule35, auxRule1 == rule36, auxRule1 == rule37, auxRule1 == rule38,
                         auxRule1 == rule39))
                v.add(Or(auxRule2 == rule30, auxRule2 == rule31, auxRule2 == rule32, auxRule2 == rule33,
                         auxRule2 == rule34,
                         auxRule2 == rule35, auxRule2 == rule36, auxRule2 == rule37, auxRule2 == rule38,
                         auxRule2 == rule39))
                auxRule3 = Const('auxRule3', rules)
                v.add(Not(Exists([auxRes1, auxRes2],
                                 And(And(auxRes1 != r0, auxRes1 != r1, auxRes1 != r2, auxRes1 != r3, auxRes1 != r4,
                                         auxRes1 != r5, auxRes1 != r6, auxRes1 != r7, auxRes1 != r8, auxRes1 != r9,
                                         auxRes1 != r10, auxRes1 != r11, auxRes1 != r12, auxRes1 != r13, auxRes1 != r14,
                                         auxRes1 != r15, auxRes1 != r16, auxRes1 != r17, auxRes1 != r18, auxRes1 != r19),
                                     And(auxRes2 != r0, auxRes2 != r1, auxRes2 != r2, auxRes2 != r3, auxRes2 != r4,
                                         auxRes2 != r5, auxRes2 != r6, auxRes2 != r7, auxRes2 != r8, auxRes2 != r9,
                                         auxRes2 != r10, auxRes2 != r11, auxRes2 != r12, auxRes2 != r13, auxRes2 != r14,
                                         auxRes2 != r15, auxRes2 != r16, auxRes2 != r17, auxRes2 != r18, auxRes2 != r19)
                                     ))))
                v.add(Not(Exists([auxSub1, auxSub2],
                                 And(And(auxSub1 != s0, auxSub1 != s1, auxSub1 != s2, auxSub1 != s3, auxSub1 != s4,
                                         auxSub1 != s5, auxSub1 != s6, auxSub1 != s7, auxSub1 != s8, auxSub1 != s9,
                                         auxSub1 != s10, auxSub1 != s11, auxSub1 != s12, auxSub1 != s13, auxSub1 != s14,
                                         auxSub1 != s15, auxSub1 != s16, auxSub1 != s17, auxSub1 != s18, auxSub1 != s19),
                                     And(auxSub2 != s0, auxSub2 != s1, auxSub2 != s2, auxSub2 != s3, auxSub2 != s4,
                                         auxSub2 != s5, auxSub2 != s6, auxSub2 != s7, auxSub2 != s8, auxSub2 != s9,
                                         auxSub2 != s10, auxSub2 != s11, auxSub2 != s12, auxSub2 != s13, auxSub2 != s14,
                                         auxSub2 != s15, auxSub2 != s16, auxSub2 != s17, auxSub2 != s18, auxSub2 != s19)
                                     ))))
                v.add(Or(auxRule3 == rule30, auxRule3 == rule31, auxRule3 == rule32, auxRule3 == rule33,
                         auxRule3 == rule34, auxRule3 == rule35, auxRule3 == rule36, auxRule3 == rule37,
                         auxRule3 == rule38, auxRule3 == rule39))
                v.add(Not(Exists([auxRule1, auxRule2],
                                 And(And(auxRule2 != rule30, auxRule2 != rule31, auxRule2 != rule32, auxRule2 != rule33,
                                         auxRule2 != rule34, auxRule2 != rule35, auxRule2 != rule36, auxRule2 != rule37,
                                         auxRule2 != rule38, auxRule2 != rule39),
                                     And(auxRule1 != rule30, auxRule1 != rule31, auxRule1 != rule32, auxRule1 != rule33,
                                         auxRule1 != rule34, auxRule1 != rule35, auxRule1 != rule36, auxRule1 != rule37,
                                         auxRule1 != rule38, auxRule1 != rule39)))))
                v.add(Not(Exists(auxCon,
                                 And(auxCon != c1, auxCon != c2, auxCon != c0))))
                for formula in dictOfFormulas.keys():
                    if formula == 'Subject_Graph':
                        predicate = eval(
                            dictOfFormulas['Subject_Graph'].replace('(Not(s', '(Not(auxSub1 == s').replace(', Not(s',
                                                                                                           ', Not(auxSub2 == s')
                        )
                        v.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                            Sub_Graph(auxSub1, auxSub2) == True,
                                                            Sub_Graph(auxSub1, auxSub2) == False)
                                     )
                              )
                    if formula == 'Resources_Graph':
                        predicate = eval(
                            dictOfFormulas['Resources_Graph'].replace('(Not(r',
                                                                      '(Not(auxRes1 == r').replace(', Not(r',
                                                                                                   ', Not(auxRes2 == r'))
                        v.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                            Res_Graph(auxRes1, auxRes2) == True,
                                                            Res_Graph(auxRes1, auxRes2) == False)
                                     )
                              )
                    if formula == 'Transitive_Closure_Subject_Graph':
                        predicate = eval(
                            dictOfFormulas['Transitive_Closure_Subject_Graph'].replace('(Not(s',
                                                                                       '(Not(auxSub1 == s').replace(
                                ', Not(s',
                                ', Not(auxSub2 == s')
                        )
                        v.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                            Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                                            Subject_Closure_Graph(auxSub1, auxSub2) == False)
                                     )
                              )
                    if formula == 'Transitive_Closure_Resources_Graph':
                        predicate = eval(
                            dictOfFormulas['Transitive_Closure_Resources_Graph'].replace('(Not(r',
                                                                                         '(Not(auxRes1 == r').replace(
                                ', Not(r',
                                ', Not(auxRes2 == r'))
                        v.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                            Resource_Closure_Graph(auxRes1, auxRes2) == True,
                                                            Resource_Closure_Graph(auxRes1, auxRes2) == False)
                                     )
                              )
                    if formula == 'REQUEST_T':
                        predicate = eval(
                            dictOfFormulas['REQUEST_T'].replace(', Not(r', ', Not(auxRes1 == r').replace('Not(s',
                                                                                                 'Not(auxSub1 == s'))
                        v.add(ForAll([auxSub1, auxRes1], If(predicate,
                                                            REQUEST_T(auxSub1, auxRes1) == True,
                                                            REQUEST_T(auxSub1, auxRes1) == False)))

                    if formula == 'rule_modality':
                        predicate = eval(
                            dictOfFormulas['rule_modality'].replace(', Not(p', ', Not(auxModality == p').replace(
                                'Not(rule', 'Not(auxRule1 == rule'))
                        v.add(ForAll([auxRule1, auxModality], If(predicate,  # If it is this
                                                                 rule_modality(auxRule1, auxModality) == True,
                                                                 # Then True
                                                                 rule_modality(auxRule1,
                                                                               auxModality) == False)))  # Else -> False)

                    if formula == 'rule_subject':
                        predicate = eval(
                            dictOfFormulas['rule_subject'].replace(', Not(s', ', Not(auxSub1 == s').replace(
                                'Not(rule', 'Not(auxRule1 == rule'))
                        v.add(ForAll([auxRule1, auxSub1], If(predicate,  # If it is this
                                                             rule_subject(auxRule1, auxSub1) == True,  # Then True
                                                             rule_subject(auxRule1,
                                                                          auxSub1) == False)))  # Else -> False)

                    if formula == 'rule_resource':
                        predicate = eval(
                            dictOfFormulas['rule_resource'].replace(', Not(r', ', Not(auxRes1 == r').replace(
                                'Not(rule', 'Not(auxRule1 == rule'))
                        v.add(ForAll([auxRule1, auxRes1], If(predicate,  # If it is this
                                                             rule_resource(auxRule1, auxRes1) == True,  # Then True
                                                             rule_resource(auxRule1,
                                                                           auxRes1) == False)))  # Else -> False)

                    if formula == 'rule_condition':
                        predicate = eval(dictOfFormulas['rule_condition'].replace(
                            ', Not(c', ', Not(auxCon == c').replace('Not(rule', 'Not(auxRule1 == rule'))
                        v.add(ForAll([auxRule1, auxCon], If(predicate,  # If it is this
                                                            rule_condition(auxRule1, auxCon) == True,  # Then True
                                                            rule_condition(auxRule1,
                                                                           auxCon) == False)))  # Else -> False))

                    if formula == 'rule_priority':
                        predicate = eval(
                            dictOfFormulas['rule_priority'].replace(', Not(4', ', Not(auxInt == 4').replace(
                                ', Not(2', ', Not(auxInt == 2').replace(
                                ', Not(3', ', Not(auxInt == 3').replace(
                                ', Not(0', ', Not(auxInt == 0').replace(
                                ', Not(1', ', Not(auxInt == 1').replace('Not(rule', 'Not(auxRule1 == rule'))
                        v.add(ForAll([auxRule1, auxInt], If(predicate,  # If it is this
                                                            rule_priority(auxRule1, auxInt) == True,  # Then True
                                                            rule_priority(auxRule1,
                                                                          auxInt) == False)))  # Else -> False))

                    if formula == 'lessSpecific':
                        predicate = eval(dictOfFormulas['lessSpecific'].replace(', Not(r', ', Not(auxRule2 == r').replace(
                            'Not(r', 'Not(auxRule1 == r'))
                        v.add(ForAll([auxRule1, auxRule2], If(predicate,
                                                              lessSpecific(auxRule1, auxRule2),
                                                              Not(lessSpecific(auxRule1, auxRule2)))))

                    if formula == 'conRule':
                        predicate = eval(dictOfFormulas['conRule'].replace(', r', ', auxRule1 == r').replace(
                            'c', 'auxCon == c'))
                        v.add(ForAll([auxRule1, auxCon], If(predicate,
                                                            conRule(auxCon, auxRule1),
                                                            Not(conRule(auxCon, auxRule1)))))

                    if formula == 'applicable':
                        predicate = eval(dictOfFormulas['applicable'].replace(
                            ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                                     'And(auxSub1 == s'))
                        v.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                      applicable(auxSub1, auxRes1, auxRule1),
                                                                      Not(applicable(auxSub1, auxRes1, auxRule1)))))

                    if formula == 'notDomainSub':
                        predicate = eval(dictOfFormulas['notDomainSub'].replace('(s', '(auxSub1 == s').replace(', s',
                                                                                                               ', auxSub1 == s'))
                        v.add(ForAll([auxSub1], If(predicate,
                                                   notDomainSUB(auxSub1),
                                                   Not(notDomainSUB(auxSub1)))))

                    if formula == 'notDomainRes':
                        predicate = eval(dictOfFormulas['notDomainRes'].replace('(r', '(auxRes1 == r').replace(', r',
                                                                                                               ', auxRes1 == r'))
                        v.add(ForAll([auxRes1], If(predicate,
                                                   notDomainRES(auxRes1),
                                                   Not(notDomainRES(auxRes1)))))

                    if formula == 'maxElem':
                        predicate = eval(dictOfFormulas['maxElem'].replace(
                            ', Not(rule', ', Not(auxRule1 == rule').replace(', Not(r', ', Not(auxRes1 == r').replace('Not(s',
                                                                                                     'Not(auxSub1 == s'))
                        v.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                      maxElem(auxSub1, auxRes1, auxRule1),
                                                                      Not(maxElem(auxSub1, auxRes1, auxRule1)))))

                    if formula == 'isPrecededBy':
                        dictOfFormulas['isPrecededBy'] = dictOfFormulas['isPrecededBy'].replace(', rule',
                                                                                                ', auxRule1 == rule').replace(
                            'And(s', 'And(auxSub1 == s').replace(', r', ', auxRes1 == r')

                        matches = re.finditer(r"auxRule1", dictOfFormulas['isPrecededBy'], re.MULTILINE)

                        for matchNum, match in enumerate(matches, start=1):
                            if matchNum % 2 == 0:
                                dictOfFormulas['isPrecededBy'] = list(dictOfFormulas['isPrecededBy'])
                                dictOfFormulas['isPrecededBy'][match.end() - 1] = '2'
                                dictOfFormulas['isPrecededBy'] = "".join(dictOfFormulas['isPrecededBy'])

                        predicate = eval(dictOfFormulas['isPrecededBy'])
                        v.add(ForAll([auxSub1, auxRes1, auxRule1, auxRule2],
                                     If(predicate,
                                        isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                                        Not(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2)))))

                    if formula == 'pseudoSink':
                        predicate = eval(dictOfFormulas['pseudoSink'].replace('And(s', 'And(auxSub1 == s').replace(
                            ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace(', c', ', auxCon == c'))
                        v.add(ForAll([auxSub1, auxRes1, auxCon, auxRule1],
                                     If(predicate,
                                        pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                        Not(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1)))))

                    # Declaring the four properties
                    accessibility = Function('Accessibility', V_SUB, V_RES, CONTEXT, BoolSort())
                    #auxRes1 = Const('auxRes1', V_RES)
                    #auxSub1 = Const('auxSub1', V_SUB)
                    #auxRule1 = Const('auxRule1', rules)
                    #auxCon = Const('auxCon', CONTEXT)
                    v.add(ForAll([auxSub1, auxRes1, auxCon],
                                 If(And(ForAll([auxRule1], Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                                                   rule_modality(auxRule1, permission)
                                                                   )
                                               ),
                                        Exists(auxRule1, pseudoSink(auxSub1, auxRes1, auxCon, auxRule1))
                                        ),
                                    accessibility(auxSub1, auxRes1, auxCon),
                                    Not(accessibility(auxSub1, auxRes1, auxCon))
                                    )
                                 )
                          )

                    # xx, yy = Ints("xx yy")
                    # condition0, condition1, condition2 = Bools("c0 c1 c2")
                    # condition0 = xx > 0
                    # condition1 = xx > yy
                    # condition2 = yy == 10
                    #
                    # linkingContextAndConditions = Function('LinkingContextAndConditions', CONTEXT, BoolSort(),
                    #                                        BoolSort())
                    # auxCondition = Const('auxCondition', BoolSort())

                    # linkingContextAndConditions(c0, condition0), linkingContextAndConditions(c1, condition1),
                    # linkingContextAndConditions(c2, condition2))
                    # s.add(ForAll([auxCon, auxCondition], If(Or(And(auxCon == c0, auxCondition == condition0),
                    #                                            And(auxCon == c1, auxCondition == condition1),
                    #                                            And(auxCon == c2, auxCondition == condition2)),
                    #                                         linkingContextAndConditions(auxCon, auxCondition),
                    #                                         Not(linkingContextAndConditions(auxCon, auxCondition)
                    #                                             )
                    #                                         )
                    #              )
                    #       )

                    # accessibilityWithConditions = Function('AccessibilityWithConditions', V_SUB, V_RES, CONTEXT,
                    #                                        BoolSort())
                    # auxRes1 = Const('auxRes1', V_RES)
                    # auxSub1 = Const('auxSub1', V_SUB)
                    # auxRule1 = Const('auxRule1', rules)
                    # auxCon = Const('auxCon', CONTEXT)
                    # auxCondition = Const('auxCondition', BoolSort())
                    # s.add(ForAll([auxSub1, auxRes1, auxCon],
                    #              If(And(ForAll([auxRule1], Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                    #                                                rule_modality(auxRule1, permission)
                    #                                                )
                    #                            ),
                    #                     Exists(auxRule1, pseudoSink(auxSub1, auxRes1, auxCon, auxRule1)),
                    #                     ForAll(auxCondition, Implies(linkingContextAndConditions(auxCon, auxCondition),
                    #                                                  auxCondition))
                    #                     ),
                    #                 accessibilityWithConditions(auxSub1, auxRes1, auxCon),
                    #                 Not(accessibilityWithConditions(auxSub1, auxRes1, auxCon))
                    #                 )
                    #              )
                    #       )

                    hiddenDocument = Function('HiddenDocument', CONTEXT, BoolSort())
                    #auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
                    #auxSub1 = Const('auxSub1', V_SUB)
                    #auxCon = Const('auxCon', CONTEXT)
                    #auxRule1 = Const('auxRule1', rules)
                    v.add(ForAll(auxCon,
                                 If(Exists(auxRes1,
                                           And(notDomainRES(auxRes1),
                                               ForAll([auxSub1],
                                                      Implies(REQUEST_T(auxSub1, auxRes1),
                                                              Not(And(ForAll(auxRule1,
                                                                             Implies(pseudoSink(auxSub1, auxRes1,
                                                                                                auxCon, auxRule1),
                                                                                     rule_modality(auxRule1, permission)
                                                                                 )
                                                                             ),
                                                                      Exists(auxRule1,
                                                                             pseudoSink(auxSub1, auxRes1, auxCon,
                                                                                        auxRule1)))
                                                                  )
                                                              )
                                                      )
                                               )
                                           ),
                                    hiddenDocument(auxCon),
                                    Not(hiddenDocument(auxCon)
                                        )
                                    )
                                 )
                          )

                    hiddenDataSet = Function('hiddenDataSet', CONTEXT, V_RES, BoolSort())
                    #auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
                    #auxSub1 = Const('auxSub1', V_SUB)
                    #auxCon = Const('auxCon', CONTEXT)
                    #auxRule1 = Const('auxRule1', rules)
                    v.add(ForAll([auxCon, auxRes1],
                                 If(And(notDomainRES(auxRes1),
                                        ForAll([auxSub1, auxRes2],
                                               Implies(And(REQUEST_T(auxSub1, auxRes2),
                                                           auxRes2 == auxRes1),
                                                       Not(And(ForAll(auxRule1,
                                                                      Implies(pseudoSink(auxSub1, auxRes1, auxCon,
                                                                                         auxRule1),
                                                                              rule_modality(auxRule1, permission))),
                                                               Exists(auxRule1, pseudoSink(auxSub1, auxRes1, auxCon,
                                                                                           auxRule1))))))),
                                    hiddenDataSet(auxCon, auxRes1),
                                    Not(hiddenDataSet(auxCon, auxRes1))
                                    )
                                 )
                          )

                    UnavailableDocument = Bool('UnavailableDocument')
                    v.add(Implies(Exists(auxRes1, ForAll([auxCon], hiddenDataSet(auxCon, auxRes1))),
                                  UnavailableDocument))
                    v.add(Implies(UnavailableDocument,
                                  Exists(auxRes1, ForAll([auxCon], hiddenDataSet(auxCon, auxRes1)))))

                    gratingContext = Function('gratingContext', V_SUB, V_RES, CONTEXT, BoolSort())
                    #auxRes1 = Const('auxRes1', V_RES)
                    #auxSub1 = Const('auxSub1', V_SUB)
                    #auxRule1 = Const('auxRule1', rules)
                    #auxCon = Const('auxCon', CONTEXT)
                    v.add(ForAll([auxSub1, auxRes1, auxCon],
                                 If(And(ForAll([auxRule1], Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                                                   rule_modality(auxRule1, permission)
                                                                   )
                                               ),
                                        Exists(auxRule1, pseudoSink(auxSub1, auxRes1, auxCon, auxRule1))
                                        ),
                                    gratingContext(auxSub1, auxRes1, auxCon),
                                    Not(gratingContext(auxSub1, auxRes1, auxCon))
                                    )
                                 )
                          )

                    ineffectiveSet = Function('ineffectiveSet', rules, BoolSort())
                    #auxRes1 = Const('auxRes1', V_RES)
                    #auxSub1 = Const('auxSub1', V_SUB)
                    #auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
                    #auxCon = Const('auxCon', CONTEXT)
                    v.add(ForAll([auxRule1],
                                 If(Not(Exists([auxSub1, auxRes1, auxCon],
                                               And(REQUEST_T(auxSub1, auxRes1),
                                                   conRule(auxCon, auxRule1),
                                                   pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                                   Or(Not(Exists(auxRule2, And(pseudoSink(auxSub1, auxRes1, auxCon,
                                                                                          auxRule2),
                                                                               auxRule1 != auxRule2))),
                                                      And(rule_modality(auxRule1, prohibition),
                                                          ForAll(auxRule2, Implies(And(pseudoSink(auxSub1, auxRes1,
                                                                                                  auxCon, auxRule2),
                                                                                       auxRule1 != auxRule2),
                                                                                   rule_modality(auxRule2, permission)))
                                                          )
                                                      )))),
                                    ineffectiveSet(auxRule1),
                                    Not(ineffectiveSet(auxRule1))
                                    )
                                 )
                          )


                print(v.check())
                if v.check() == sat:
                    f = open("model5.txt", "w+")
                    for variable in v.model():
                        f.write(str(variable)), f.write("="), f.write(str(v.model()[variable])), f.write("\n")
                    f.close()

                    dictOfSubstitutions = dict()
                    chosenVariables = [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17,
                                       s18,
                                       s19,
                                       r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,
                                       r18,
                                       r19,
                                       rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39,
                                       c0,
                                       c1, c2,
                                       permission, prohibition]

                    # Rewriting the variables
                    for variable in chosenVariables:
                        with open("model5.txt") as f:
                            for line in f:
                                matches = re.finditer(r"" + str(variable) + "=", line)
                                for matchNum, match in enumerate(matches):
                                    dictOfSubstitutions[variable] = line[match.end():len(line) - 1:]
                        f.close()

                    with open("model5.txt", 'r') as f:
                        modelContent = f.read()
                    f.close()
                    for key in dictOfSubstitutions.keys():
                        modelContent = re.sub(r"\b%s\b" % dictOfSubstitutions[key], str(key), modelContent, 0,
                                              re.MULTILINE)
                    # Erasing the k!#### and replacing for the variables
                    modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
                    # Erasing k!#### variables
                    modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
                    # Erasing weird syntax from the solver (If(Var(0) == ...)
                    modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "",
                                          modelContent)
                    modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
                    modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
                    # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
                    modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
                    modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
                    modelContent = re.sub(r"\[ Or", "[Or", modelContent)
                    f = open("model5.txt", "w+")
                    f.write(modelContent)
                    f.close()

print(time.time() - ts)
