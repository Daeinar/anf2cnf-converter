#!/usr/bin/env python3

import itertools
import os
import re
import sys

"""
====================================================================================
 Polynomial class
====================================================================================
"""
class Poly():
  def __init__(self):
    self._deg = 0

    # The support of the polynomial sorted by degree.
    self._support = dict() 

  # Return the degree of the polynomial.
  # def _get_deg(self): return self._deg

  # Return all terms of a certain degree.
  def _get_terms_by_deg(self,deg): 
    if deg in self._support:
      return self._support[deg]
    else:
      return []

  # Add a term (in list format) to the polynomial.  The operation respects the
  # involutive property of the addition in F_2. 
  def _add_term(self,term):

    # First term of a degree.
    if len(term) not in self._support:
      self._support[len(term)] = [term]
      if self._deg < len(term): 
        self._deg = len(term)

    # There are already other terms of a degree.
    else:
      terms = self._support[len(term)]
      if term not in terms:
        terms.append(term)
      else:
        terms.remove(term)
      # Last term of that particular degree.
      if terms == []:
        del self._support[len(term)]
        # Check if any elements are left in the polynomial.
        if len(self._support.keys()) > 0:
          # Update the degree.
          self._deg = max(self._support.keys())
        else: self._deg = -1
      # Update terms of that degree.
      else:
        self._support[len(term)] = terms

  # Return the polynomial in string format.
  def to_string(self):
    l = []
    for deg in list(self._support.keys())[::-1]:
      s = self._support[deg]
      for i in range(len(s)):
          l.append(str(s[i]))
    return ' + '.join(l)


"""
====================================================================================
 Data class
====================================================================================
"""
class _Data():
  def __init__(self):
    self._polys = list()
    self._sub_polys = dict()
    self._sub_poly_stack = list()
    self._var_index = dict()
    self._num_indets = 0
    self._num_clauses = 0


"""
====================================================================================
 Conversion functions
====================================================================================
"""
# Converts a quadratic (cubic) system of polynomials to (XOR-)CNF-SAT.
# Data: Object of the _Data class.
# cl: Cutting length, i.e. the maximal support length of a polynomial.
# qstrategy: Substitution strategy for quadratic terms.
# cstrategy: Substitution strategy for cubic terms.
# output: Format of the output. 
#         "XOR": XOR-CNF-SAT (for cryptominisat)
#         "CNF": DIMACS CNF-SAT
def to_cnf(Data,cl,qstrategy,cstrategy,output,path):
  strategies = {
      "SS": ss,
      "LPS": lps,
      "DPS": dps,
      "QPS": qps,
      "CPS": cps
  }

  write_sub_poly = {
      "SS": write_ss,
      "LPS": write_lps,
      "DPS": write_dps,
      "QPS": write_qps,
      "CPS": write_cps
  }

  ofile = open(path+".tmp",'a')

  for i in range(len(Data._polys)):

    #print("Polynomial:",Data._polys[i].to_string())
  
    # Linearize the polynomial.
    while len(Data._polys[i]._get_terms_by_deg(3)) != 0:
      term = Data._polys[i]._get_terms_by_deg(3).pop(0)
      strategies[cstrategy](Data,term,i)

    while len(Data._polys[i]._get_terms_by_deg(2)) != 0:
      term = Data._polys[i]._get_terms_by_deg(2).pop(0)
      strategies[qstrategy](Data,term,i)

    # Write new substitution polynomials to file.
    while len(Data._sub_poly_stack) != 0:
      sub_poly = Data._sub_poly_stack.pop(0)
      c = write_sub_poly[sub_poly[0]](sub_poly,ofile)
      Data._num_clauses += c

    #print("Linearized:",Data._polys[i].to_string())

    # Write linearized polynomial to file
    if output == "XOR":
      c = write_xor_poly(Data._polys[i],ofile)
      Data._num_clauses += c
    elif output == "CNF":
      l = cut_poly(Data,i,cl)
      for j in range(len(l)):
        #print(j,":",l[j].to_string())
        c = write_cnf_poly(l[j],ofile)
        Data._num_clauses += c

  ofile.close()
  ofile = open(path+".tmp",'r')
  contents = ofile.read()
  ofile.close()

  # Write the header and copy the clauses to the final CNF file.
  out = open(path,'a')
  out.write("p cnf {} {}\n".format(Data._num_indets,Data._num_clauses))
  out.write(contents)
  out.close()

  # Delete temp file.
  os.remove(path+".tmp")


"""
====================================================================================
 Substitution strategies
====================================================================================
"""
# Perform the substitution of a term.
def substitute(Data,sub_poly,index):

  # Construct the dicitionary key. (Note: sub_poly[0] contains the type, which is
  # not needed for the key)
  key = ' + '.join([str(sub_poly[i]) for i in range(1,len(sub_poly))])

  if key not in Data._sub_polys:
    Data._num_indets = Data._num_indets + 1
    Data._sub_polys[key] = [Data._num_indets]
    Data._polys[index]._add_term([Data._num_indets])
    sub_poly.append([Data._num_indets])
    Data._sub_poly_stack.append(sub_poly)
  else:
    subIndet = Data._sub_polys[key]
    Data._polys[index]._add_term(subIndet)


# Standard substitution.
def ss(Data,term,index):
  substitute(Data,["SS",term],index)


# Cut the poly according to the cutting length cl.
def cut_poly(Data,index,cl):
  poly_list = []
  lin_terms = Data._polys[index]._get_terms_by_deg(1)
  f = Poly()
  for i in range(len(lin_terms)):
    if len(f._get_terms_by_deg(1)) == cl - 1:
      Data._num_indets += 1
      f._add_term([Data._num_indets])
      poly_list.append(f)
      f = Poly()
      f._add_term([Data._num_indets])

    f._add_term(lin_terms[i])
  
    if (i == len(lin_terms) - 1):
      if len(Data._polys[index]._get_terms_by_deg(0)) == 1:
        f._add_term(Data._polys[index]._get_terms_by_deg(0)[0])
      poly_list.append(f)
  return poly_list


"""
====================================================================================
 Strategies for quadratic terms
====================================================================================
"""
# Linear Partner Substitution.
def lps(Data,term,index):
  i = -1
  # Check for linear partners.
  if [term[0]] in Data._polys[index]._get_terms_by_deg(1):
    i = 0 
  elif [term[1]] in Data._polys[index]._get_terms_by_deg(1):
    i = 1
  # Linear partner found.
  if (i == 0) or (i == 1):
    # Remove linear partner from the polynomial.
    Data._polys[index]._add_term([term[i]])
    # Construct the term list for the substitution polynomial.
    sub_poly = ["LPS",term,[term[i]]]
    substitute(Data,sub_poly,index)
  # No linear partner found.
  else:
    ss(Data,term,index)


# Double Partner Substitution.
def dps(Data,term,index):
  if ([term[0]] in Data._polys[index]._get_terms_by_deg(1)) and \
    ([term[1]] in Data._polys[index]._get_terms_by_deg(1)) and \
    ([] in Data._polys[index]._get_terms_by_deg(0)):

    # Remove linear partners from the polynomial.
    Data._polys[index]._add_term([term[0]])
    Data._polys[index]._add_term([term[1]])
    Data._polys[index]._add_term([])
    sub_poly = ["DPS",term,[term[0]],[term[1]],[]]
    substitute(Data,sub_poly,index)
  else:
    lps(Data,term,index)


# Quadratic Partner Substitution.
def qps(Data,term,index):
  x = False
  terms = Data._polys[index]._get_terms_by_deg(2)
  for t in terms:
    u = set.intersection(set(term),set(t))
    if len(u) == 1:
      x = True
      # Remove the quadratic partner from the polynomial.
      Data._polys[index]._add_term(t)
      sub_poly = ["QPS",term,t]
      substitute(Data,sub_poly,index)
      break
  if x == False:
    ss(Data,term,index)


"""
====================================================================================
 Strategies for cubic terms
====================================================================================
"""
# Cubic Partner Substitution.
def cps(Data,term,index):
  x = False
  terms = Data._polys[index]._get_terms_by_deg(3)
  for t in terms:
    u = set.intersection(set(term),set(t))
    if len(u) == 2:
      x = True
      # Remove the cubic partner from the polynomial.
      Data._polys[index]._add_term(t)
      sub_poly = ["CPS",term,t]
      substitute(Data,sub_poly,index)
      break
  if x == False:
    ss(Data,term,index)


"""
====================================================================================
 CNF / XOR writing functions
====================================================================================
"""
def write_clauses(l,ofile):
  for i in range(len(l)):
    ofile.write("{}\n".format(l[i]))


def write_ss(p,ofile):
  # List of clauses. 
  c = []
  #print(p)
  # Number of clauses.
  if len(p[1]) == 2:
    c.append(''.join([str(p[1][0])," -",str(p[2][0])," 0"]))
    c.append(''.join([str(p[1][1])," -",str(p[2][0])," 0"]))
    c.append(''.join(["-",str(p[1][0])," -",str(p[1][1])," ",str(p[2][0])," 0"]))
  elif len(p[1]) == 3:
    c.append(''.join([str(p[1][0])," -",str(p[2][0])," 0"]))
    c.append(''.join([str(p[1][1])," -",str(p[2][0])," 0"]))
    c.append(''.join([str(p[1][2])," -",str(p[2][0])," 0"]))
    c.append(''.join(["-",str(p[1][0])," -",str(p[1][1])," -",str(p[1][2])," ",str(p[2][0])," 0"]))
  write_clauses(c,ofile)
  return len(c)


def write_lps(p,ofile):
  c = []
  #print(p)
  # Move the partner indet to the first slot in the quadratic term.
  if p[1][1] == p[2][0]:
    p[1][0], p[1][1] = p[1][1], p[1][0]
  c.append(''.join([str(p[1][0])," -",str(p[3][0])," 0"]))
  c.append(''.join(["-",str(p[1][1])," -",str(p[3][0])," 0"]))
  c.append(''.join(["-",str(p[1][0])," ",str(p[1][1])," ",str(p[3][0])," 0"]))
  write_clauses(c,ofile)
  return len(c)


def write_dps(p,ofile):
  c = []
  #print(p)
  c.append(''.join(["-",str(p[1][0])," -",str(p[5][0])," 0"]))
  c.append(''.join(["-",str(p[1][1])," -",str(p[5][0])," 0"]))
  c.append(''.join([str(p[1][0])," ",str(p[1][1])," ",str(p[5][0])," 0"]))
  write_clauses(c,ofile)
  return len(c)


def write_qps(p,ofile):
  c = []
  #print(p)
  # Compute the common indet.
  i = (set(p[1]) & set(p[2])).pop()
  # Sort the quadratic terms s.t. the common indet is in the first slot.
  if p[1][0] != i:
    p[1][0], p[1][1] = p[1][1],p[1][0]
  if p[2][0] != i:
    p[2][0], p[2][1] = p[2][1],p[2][0]
  c.append(''.join([str(p[1][0])," -",str(p[3][0])," 0"]))
  c.append(''.join([str(p[1][1])," ",str(p[2][1])," -",str(p[3][0])," 0"]))
  c.append(''.join(["-",str(p[1][1])," -",str(p[2][1])," -",str(p[3][0])," 0"]))
  c.append(''.join(["-",str(p[1][0])," -",str(p[1][1])," ",str(p[2][1])," ",str(p[3][0])," 0"]))
  c.append(''.join(["-",str(p[1][0])," ",str(p[1][1])," -",str(p[2][1])," ",str(p[3][0])," 0"]))
  write_clauses(c,ofile)
  return len(c)


def write_cps(p,ofile):
  c = []
  #print(p)
  # Compute the common indets.
  i = list(set(p[1]) & set(p[2]))
  j = list(set(p[1]).difference(set(i)))
  k = list(set(p[2]).difference(set(i)))
  # Sort the cubic terms s.t. the common indets are in the first two slots.
  p[1] = [i[0],i[1],j[0]]
  p[2] = [i[0],i[1],k[0]]
  c.append(''.join([str(p[1][0])," -",str(p[3][0])," 0"]))
  c.append(''.join([str(p[1][1])," -",str(p[3][0])," 0"]))
  c.append(''.join([str(p[1][2])," ",str(p[2][2])," -",str(p[3][0])," 0"]))
  c.append(''.join(["-",str(p[1][2])," -",str(p[2][2])," -",str(p[3][0])," 0"]))
  c.append(''.join(["-",str(p[1][0])," -",str(p[1][1])," -",str(p[1][2])," ",str(p[2][2])," ",str(p[3][0])," 0"]))
  c.append(''.join(["-",str(p[1][0])," -",str(p[1][1])," ",str(p[1][2])," -",str(p[2][2])," ",str(p[3][0])," 0"]))
  write_clauses(c,ofile)
  return len(c)


def write_xor_poly(poly,ofile):
  # Note: If the support does not include the constant factor 1, we invert the
  # first variable. This way the whole XOR formula gets inverted. 
  if len(poly._get_terms_by_deg(0)) == 1:
    s = "x"
  else:
    s = "x-"
  ofile.write("{}\n".format(s + ' '.join([str(t[0]) for t in \
    poly._get_terms_by_deg(1)[::-1]]) + " 0"))
  return 1


def write_cnf_poly(poly,ofile):
  # Flatten list of linear terms. 
  t = [str(u[0]) for u in poly._get_terms_by_deg(1)]
  c = []

  # Polynomial has no constant term.
  if len(poly._get_terms_by_deg(0)) == 0 :
    # x[1] + x[2]
    if len(t) == 2:
      c.append(''.join([    t[0]," -",t[1]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," 0"]))

    # x[1] + x[2] + x[3]
    elif len(t) == 3:
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2]," 0"]))

    # x[1] + x[2] + x[3] + x[4]
    elif len(t) == 4:
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2], " ",t[3]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2], " ",t[3]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2], " ",t[3]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2]," -",t[3]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2], " ",t[3]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2]," -",t[3]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2]," -",t[3]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2]," -",t[3]," 0"]))

    # x[1] + x[2] + x[3] + x[4] + x[5]
    elif len(t) == 5:
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2], " ",t[3], " ",t[4]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2], " ",t[3], " ",t[4]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2], " ",t[3], " ",t[4]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2]," -",t[3], " ",t[4]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2], " ",t[3]," -",t[4]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2], " ",t[3], " ",t[4]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2]," -",t[3], " ",t[4]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2], " ",t[3]," -",t[4]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2], " ",t[3]," -",t[4]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2]," -",t[3]," -",t[4]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2]," -",t[3], " ",t[4]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2]," -",t[3]," -",t[4]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2]," -",t[3]," -",t[4]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2], " ",t[3]," -",t[4]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2]," -",t[3], " ",t[4]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2]," -",t[3]," -",t[4]," 0"]))

    # x[1] + x[2] + x[3] + x[4] + x[5] + x[6]
    elif len(t) == 6:
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2], " ",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2], " ",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2], " ",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2]," -",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2], " ",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2], " ",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2], " ",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2]," -",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2], " ",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2], " ",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2]," -",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2], " ",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2], " ",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2]," -",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2]," -",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2], " ",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2]," -",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2], " ",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2], " ",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2]," -",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2]," -",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2], " ",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2]," -",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2]," -",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2], " ",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2]," -",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2]," -",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2]," -",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2], " ",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2]," -",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2]," -",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2]," -",t[3]," -",t[4]," -",t[5]," 0"]))

  # Polynomial has a constant term.
  else:
    # x[1] + x[2] + 1
    if len(t) == 2:
      c.append(''.join(["-",t[0]," -",t[1]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," 0"]))

    # x[1] + x[2] + x[3] + 1
    elif len(t) == 3:
      c.append(''.join([    t[0], " ",t[1], " ",t[2]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2]," 0"]))

    # x[1] + x[2] + x[3] + x[4] + 1
    elif len(t) == 4:
      c.append(''.join([    t[0], " ",t[1], " ",t[2], " ",t[3]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2], " ",t[3]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2], " ",t[3]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2]," -",t[3]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2], " ",t[3]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2]," -",t[3]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2]," -",t[3]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2]," -",t[3]," 0"]))

    # x[1] + x[2] + x[3] + x[4] + x[5] + 1
    elif len(t) == 5:
      c.append(''.join([    t[0], " ",t[1], " ",t[2], " ",t[3], " ",t[4]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2], " ",t[3], " ",t[4]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2], " ",t[3], " ",t[4]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2]," -",t[3], " ",t[4]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2], " ",t[3]," -",t[4]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2], " ",t[3], " ",t[4]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2]," -",t[3], " ",t[4]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2], " ",t[3]," -",t[4]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2]," -",t[3], " ",t[4]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2], " ",t[3]," -",t[4]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2]," -",t[3]," -",t[4]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2]," -",t[3], " ",t[4]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2], " ",t[3]," -",t[4]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2]," -",t[3]," -",t[4]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2]," -",t[3]," -",t[4]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2]," -",t[3]," -",t[4]," 0"]))

    # x[1] + x[2] + x[3] + x[4] + x[5] + x[6] + 1
    elif len(t) == 6:
      c.append(''.join([    t[0], " ",t[1], " ",t[2], " ",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2], " ",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2], " ",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2]," -",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2], " ",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2], " ",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2], " ",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2]," -",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2], " ",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2], " ",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2]," -",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2], " ",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2], " ",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2]," -",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2]," -",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1], " ",t[2], " ",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2]," -",t[3], " ",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2], " ",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2]," -",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2]," -",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2]," -",t[3]," -",t[4], " ",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2], " ",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2]," -",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2]," -",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2]," -",t[3], " ",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1], " ",t[2], " ",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1]," -",t[2], " ",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1]," -",t[2], " ",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0], " ",t[1], " ",t[2]," -",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0]," -",t[1], " ",t[2]," -",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join([    t[0], " ",t[1]," -",t[2]," -",t[3]," -",t[4]," -",t[5]," 0"]))
      c.append(''.join(["-",t[0]," -",t[1]," -",t[2]," -",t[3]," -",t[4]," -",t[5]," 0"]))

  write_clauses(c,ofile)

  return len(c)



"""
====================================================================================
 Input processing functions 
====================================================================================
"""
# Enumerate the variables and save the informations to a dictionary.
# Format: [indetname : indetindex]
def create_var_index(config,Data):
  indets = config.rstrip().split(';')
  counter = 1
  for i in range(len(indets)):
    varname = indets[i][0]
    indices = indets[i][1:].strip('[]').split(',')
    iranges = list() # index ranges
    # Expand indices.
    for j in range(len(indices)):
      t = tuple(indices[j].split('..'))
      iranges.append(list(range(int(t[0]),int(t[len(t)-1])+1)))

    # Recombine the indices and save them to the var_index dictionary.
    for ituple in itertools.product(*iranges):
      Data._var_index[varname+str(list(ituple)).replace(" ","")] = counter
      counter += 1
  Data._num_indets = len(Data._var_index)


# Reads polynomials and writes them to a Data class object.
def read_polys(path,Data):
  with open(path, encoding='utf-8') as infile:
    # Read the first line, which contains the configuration of the indeterminates.
    config = infile.readline()
    create_var_index(config,Data)
    for line in infile:

      # Ignore empty lines in the input file.
      if line != '\n':
        f = Poly()
        terms = line.rstrip().split('+')
        for i in range(len(terms)):
          term = list()
          for indet in re.finditer('(([a-z]|[A-Z]){1}\[([0-9]*\,)*[0-9]+\])|(1)',terms[i]):
            if indet.group(0) != '1':
              term.append(Data._var_index[indet.group(0)])
          f._add_term(term)
        Data._polys.append(f)


# As the name suggests.
def help():
  return "Usage: anf2cny.py CNF [3-6] [SS,LPS,DPS,QPS] [SS,CPS] source target\n"+ \
         "   or: anf2cny.py XOR [SS,LPS,DPS,QPS] [SS,CPS] source target"
  


"""
====================================================================================
 Main
====================================================================================
"""
def main():
  # Set default values.
  output = "CNF"
  cl = 4
  qs = "SS"
  cs = "SS"

  # Process the input parameters.
  num_args = len(sys.argv)
  if ("--help") in sys.argv: 
  	print(help())
  	return 0 

  if (sys.argv[1] == "CNF") and (num_args == 7):
  	output = "CNF"
  	cl = int(sys.argv[2])
  	qs = sys.argv[3]
  	cs = sys.argv[4]
  elif (sys.argv[1] == "XOR") and (num_args == 6):
    output = "XOR"
    qs = sys.argv[2]
    cs = sys.argv[3]
  else:
    print("Error! Wrong (number of) parameters.")
    print(help())
    return 2

  ipath = sys.argv[num_args-2]
  opath = sys.argv[num_args-1]

  D = _Data()

  # Reset output file.
  if opath != "":
    ofile = open(opath,'w')
    ofile.close()

  # Read the polynomials from the input file.
  read_polys(ipath,D)

  # Start conversion.
  to_cnf(D,cl,qs,cs,output,opath)

if __name__ == '__main__':
  status = main()
  sys.exit(status)
