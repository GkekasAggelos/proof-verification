import re

def notinside(e, arr):
    for i in arr:
        if i == e:
            return False
    return True

def propsymbol(arr):
    lsymbols = ['¬', '∧', '∨', '→', '↔', '(', ')']
    if (len(arr) == 1)and(notinside(arr[0], lsymbols)):
        return True
    return False

def prefixindex(e):
    res = len(e)
    l = 0
    r = 0
    for i in range(len(e)):
        if e[i] == '(':
            l += 1
        if e[i] == ')':
            r += 1
        if l == r:
            return i
    return res

def isWFF(e):
    n = len(e)
    if n == 0 or n == 2:
        return False
    if n == 1:
        return propsymbol(e)
    if e[0] != '(' or e[n - 1] != ')':
        return False
    e_new = e[1:n - 1]
    if e_new[0] == '¬':
        return isWFF(e_new[1:])
    k = prefixindex(e_new)
    if k > n - 5:
        return False
    e1 = e_new[0:k + 1]
    e2 = e_new[k + 2:]
    if notinside(e_new[k + 1], ['∧', '∨', '→', '↔']):
        return False
    return isWFF(e1) and isWFF(e2)

def error1(f, i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Expression " + f + " is not a wff."
def error2(j):
    return "Error in theorem " + str(j) + ": formulas.txt and explanations.txt do not have the same number of lines."
def error3(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Explanation does not have the correct format."
def error4(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Explanation does not describe the corresponding formula."
def error5(j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": The last formula of explanations.txt is not the same as the corresponding theorem."
def error6(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Arguements of Modus Ponens must refer to previous formulas."
def error7(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Reference to theorems can be done only to previous theorems."
def error8(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Formula does not have the correct format."
def error9(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Hypotheses are not wff."
def error10(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Hypotheses of prequisites and result of Modus Ponens must be the same."
def error11(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Arguements of monotonicity must refer to previous formulas."
def error12(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Monotonicity does not hold."
def error13(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Theorems must use only previous formulas as hypotheses."
def error14(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Length of indices is not the same as length of hypotheses of corresponding theorem."
def error15(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Deduction Theorem can only be aplied to previous formulas."
def error16(i, j):
    return "Error in line " + str(i) + " of theorem " + str(j) + ": Hypotheses of prequisites and result of theorems must be the same."

def change(s, changes):
    c = []
    res = s
    for e in changes:
        c.append(e.split('='))
        if len(e.split('=')) != 2:
            return -1
    for e in c:
        res = res.replace(e[0], e[0] + "0")
    for e in c:
        res = res.replace(e[0] + "0", e[1])
    return(res)

def delete(arr, e):
    flag = True
    while flag:
        flag = False
        for i in arr:
            if i == e:
                flag = True
                arr.remove(i)

def subset(arr1, arr2):
    for e in arr1:
        if notinside(e, arr2):
            return False
    return True


def equal(arr1, arr2):
    return (subset(arr1, arr2))and(subset(arr2, arr1))

def isFormalProof(formulas, explanations, theorems, j):
    flag = True
    theorem = theorems[j]

    plainformulas = []
    hypotheses = []

    # checks that all expressions in formulas are wff
    flag2 = True
    i = 0
    while (i < len(formulas))and(flag2):
        f0 = formulas[i]
        check = re.findall("\{.*\}_", f0)
        if not len(check) == 1:
            print(f0)
            flag = False
            flag2 = False
            error = error8(i, j)
        else:
            f = f0[len(check[0]):]
            plainformulas.append(f)
            if not(isWFF(f)):
                flag = False
                flag2 = False
                error = error1(f, i, j)
            else:
                h0 = f0[1:len(check[0]) - 2]
                if h0 != "":
                    h = h0.split(',')
                    hypotheses.append(h)
                    for e in h:
                        if not(isWFF(e)):
                            flag = False
                            flag2 = False
                            error = error9(i, j)
                else:
                    hypotheses.append([])
        i += 1

    # checks that formulas and explanations have the same number of lines
    if len(formulas) != len(explanations):
        flag = False
        error = error2(j)

    # checks that theorem is the last line in formulas
    if formulas[len(formulas) - 1] != theorem:
        flag = False
        error = error5(j)

    # checks that each line of explanations correctly describes the corresponding line in formulas
    i = 0
    while (i < len(explanations))and(flag):
        exp = explanations[i]
        n = len(exp)
        
        x = re.findall("^A[1-9]\[.*\]$", exp)
        y = re.findall("^MP\[[0-9]*,[0-9]*\]$", exp)
        z = re.findall("^T[0-9]*\[.*\]\[.*\]$", exp)
        w = re.findall("^MN\[[0-9]*\]$", exp)
        u = re.findall("^HYP$", exp)
        v = re.findall("^DT\[[0-9]*\]$", exp)

        # case where line i comes from an axiom
        if len(x) == 1:
            f = change(axioms["A" + exp[1]], exp[3:n - 1].split(','))
            if f == -1:
                flag = False
                error = error3(i, j)
            elif f != plainformulas[i]:
                flag = False
                error = error4(i, j)
                    
        # case where line i comes from Modus Ponens
        elif len(y) == 1:
            indices = exp[3:n - 1].split(',')
            m = int(indices[0])
            k = int(indices[1])
            if not((m < i)and(k < i)):
                flag = False
                error = error6(i, j)
            elif "(" + plainformulas[k] + "→" + plainformulas[i] + ")" != plainformulas[m]:
                flag = False
                error = error4(i, j)
            elif not((hypotheses[m] == hypotheses[i])and(hypotheses[k] == hypotheses[i])):
                flag = False
                error = error10(i, j)

        # case where line i comes from a theorem
        elif len(z) == 1:
            prefix = re.findall("^T[0-9]*", exp)[0]
            num = int(exp[1:len(prefix)])
            if not(num < j):
                flag = False
                error = error7(i, j)
            else:
                r = re.findall("\{.*\}", theorems[num])[0]
                l = re.findall("\]\[.*\]$", exp)[0]
                args = exp[len(prefix) + 1:n - len(l)].split(',')
                plaintheorem = theorems[num][len(r) + 1:]
                f = change(plaintheorem, args)
                h = theorems[num][1:len(r) - 1].split(',')
                if h == [""]:
                    h = []
                if f == -1:
                    flag = False
                    error = error3(i, j)
                elif f != plainformulas[i]:
                    flag = False
                    error = error4(i, j)
                else:
                    indices = exp[n - len(l) + 2:n - 1].split(',')
                    if indices == [""]:
                        indices = []
                    intindices = []
                    flag2 = True
                    k = 0
                    while ((k < len(indices))and(flag2)):
                        if indices[k].isnumeric():
                            intindices.append(int(indices[k]))
                            if int(indices[k]) >= i:
                                flag2 = False
                                flag = False
                                error = error13(i, j)
                        else:
                            flag2 = False
                            flag = False
                            error = error3(i, j)
                        k += 1
                    if len(h) != len(intindices):
                        flag = False
                        error = error14(i, j)
                    else:
                        flag2 = True
                        k = 0
                        while ((k < len(intindices))and(flag2)):
                            h0 = plainformulas[intindices[k]]
                            h1 = change(h[k], args)
                            if h1 == -1:
                                flag2 = False
                                flag = False
                                error = error3(i, j)
                            elif h0 != h1:
                                flag2 = False
                                flag = False
                                error = error4(i, j)
                            elif hypotheses[intindices[k]] != hypotheses[i]:
                                flag2 = False
                                flag = False
                                error = error16(i, j) 
                            k += 1                    

        # case where line i comes from monotonicity
        elif len(w) == 1:
            num = int(exp[3:n - 1])
            if num >= i:
                flag = False
                error = error11(i, j)
            elif not(subset(hypotheses[num], hypotheses[i])):
                flag = False
                error = error12(i, j)
            elif not(plainformulas[num] == plainformulas[i]):
                flag = False
                error = error4(i, j)

        # case where line i comes from non logical axiom
        elif len(u) == 1:
            if notinside(plainformulas[i], hypotheses[i]):
                flag = False
                error = error4(i, j)

        # case where line i comes from the deduction theorem
        elif len(v) == 1:
            num = int(exp[3:n - 1])
            if num >= i:
                flag = False
                error = error14(i, j)
            else:
                fold = plainformulas[num]
                fnew = plainformulas[i]
                foldregex = fold.replace("(", "\(").replace(")", "\)")
                check = re.findall(foldregex + "\)$", fnew)
                if (len(check) != 1):
                    flag = False
                    print("here")
                    error = error4(i, j)
                else:
                    hyp = fnew[1:len(fnew) - len(check[0]) - 1]
                    hnewextended = []
                    for e in hypotheses[i]:
                        hnewextended.append(e)
                    hypotheses[i]
                    hnewextended.append(hyp)
                    if notinside(hyp, hypotheses[num])or(fnew != "(" + hyp + "→" + fold + ")")or(not(equal(hypotheses[num], hnewextended)))or(not(notinside(hyp, hypotheses[i]))):
                        flag = False
                        error = error4(i, j)
        
        # if neither of the above is true line i is incorrrect
        else:
            flag = False
            error = error3(i, j)
        
        i += 1
    
    if not(flag):
        return [False, error]
    else:
        return [True, ""]

axioms = {
    "A1": "(a→(b→a))",
    "A2": "((a→(b→c))→((a→b)→(a→c)))",
    "A3": "(((¬a)→(¬b))→(((¬a)→b)→a))",
    "A4": "((a∨b)→((¬a)→b))",
    "A5": "(((¬a)→b)→(a∨b))",
    "A6": "((a∧b)→(¬(a→(¬b))))",
    "A7": "((¬(a→(¬b)))→(a∧b))",
    "A8": "((a↔b)→((a→b)∧(b→a)))",
    "A9": "(((a→b)∧(b→a))→(a↔b))"
}

ftxt = open("formulas.txt", "r")
fstring = ftxt.read()
ftxt.close()
fstring = fstring.replace(" ", "")
formulas = fstring.split("\nnext_theorem")
for i in range(len(formulas)):
    arr = formulas[i].split('\n')
    for j in range(len(arr)):
        f0 = arr[j].replace(">", "→")
        f1 = f0.replace("|", "∨")
        f2 = f1.replace("&", "∧")
        f3 = f2.replace("~", "↔")
        f = f3.replace("-", "¬")
        arr[j] = f
    for k in range(len(arr)):
        m = 0
        while (m < len(arr[k])):
            if arr[k][m] == '#':
                arr[k] = arr[k][0:m]
            m += 1  
    delete(arr, "")    
    formulas[i] = arr

etxt = open("explanations.txt", "r")
estring = etxt.read()
etxt.close()
estring = estring.replace(" ", "")
explanations = estring.split("\nnext_theorem")
for i in range(len(explanations)):
    arr = explanations[i].split('\n')
    for j in range(len(arr)):
        f0 = arr[j].replace(">", "→")
        f1 = f0.replace("|", "∨")
        f2 = f1.replace("&", "∧")
        f3 = f2.replace("~", "↔")
        f = f3.replace("-", "¬")
        arr[j] = f
    for k in range(len(arr)):
        m = 0
        while (m < len(arr[k])):
            if arr[k][m] == '#':
                arr[k] = arr[k][0:m]
            m += 1
    delete(arr, "")
    explanations[i] = arr

ttxt = open("theorems.txt", "r")
tstring = ttxt.read()
ttxt.close()
tstring = tstring.replace(" ", "")
theorems = tstring.split('\n')
for i in range(len(theorems)):
    e0 = theorems[i].replace(">", "→")
    e1 = e0.replace("|", "∨")
    e2 = e1.replace("&", "∧")
    e3 = e2.replace("~", "↔")
    e = e3.replace("-", "¬")
    theorems[i] = e
for k in range(len(theorems)):
    m = 0
    while (m < len(theorems[k])):
        if theorems[k][m] == '#':
            theorems[k] = theorems[k][0:m]
        m += 1 
delete(theorems, "")

lt = len(theorems)
lf = len(formulas)
le = len(explanations)

s = "The number of lines in theorems.txt, the number of theorems in formulas.txt and the number of theorems in explanations.txt must all be the same."
if not((lt == lf)and(lf == le)):
    print(s)
else:
    flag = True
    for j in range(len(theorems)):
        w = isFormalProof(formulas[j], explanations[j], theorems, j)
        if w[0]:
            print("Proof of theorem " + str(j) + " is correct.")
        else:
            print(w[1])
            flag = False
            break
    if flag:
        print("All proofs are correct!!!")
