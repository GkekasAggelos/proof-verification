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

fstring = """
############## T0

{}_((a>((a>a)>a))>((a>(a>a))>(a>a)))
{}_(a>((a>a)>a))
{}_(a>(a>a))
{}_((a>(a>a))>(a>a))
{}_(a>a)

next_theorem # T1

{(-(-a))}_(-(-a))
{(-(-a))}_((-(-a))>((-a)>(-(-a))))
{(-(-a))}_((-a)>(-(-a)))
{(-(-a))}_(((-a)>(-(-a)))>(((-a)>(-a))>a))
{(-(-a))}_(((-a)>(-a))>a)
{}_((-a)>(-a))
{(-(-a))}_((-a)>(-a))
{(-(-a))}_a
{}_((-(-a))>a)

next_theorem # T2

{}_(((-a)>(-a))>(a|(-a)))
{}_((-a)>(-a))
{}_(a|(-a))

next_theorem # T3

{a}_(((-(-(-a)))>(-a))>(((-(-(-a)))>a)>(-(-a))))
{a}_((-(-(-a)))>(-a))
{a}_(((-(-(-a)))>a)>(-(-a)))
{a}_(a>((-(-(-a)))>a))
{a}_a
{a}_((-(-(-a)))>a)
{a}_(-(-a)) 
{}_(a>(-(-a)))

next_theorem # T4

{((-a)>(-b)), b}_(((-a)>(-b))>(((-a)>b)>a))
{((-a)>(-b)), b}_((-a)>(-b))
{((-a)>(-b)), b}_(((-a)>b)>a)
{((-a)>(-b)), b}_(b>((-a)>b))
{((-a)>(-b)), b}_b
{((-a)>(-b)), b}_((-a)>b)
{((-a)>(-b)), b}_a
{((-a)>(-b))}_(b>a)
{}_(((-a)>(-b))>(b>a))

next_theorem # T5

{(a>b), (b>c)}_(a>b)
{(a>b), (b>c)}_(b>c)
{(a>b), (b>c)}_((a>(b>c))>((a>b)>(a>c)))
{(a>b), (b>c)}_((b>c)>(a>(b>c)))
{(a>b), (b>c)}_(a>(b>c))
{(a>b), (b>c)}_((a>b)>(a>c))
{(a>b), (b>c)}_(a>c)

next_theorem # T6

{}_(((-(-(a&(-a))))>(-(a>(-(-a)))))>((a>(-(-a)))>(-(a&(-a)))))
{}_((-(-(a&(-a))))>(a&(-a)))
{}_((a&(-a))>(-(a>(-(-a)))))
{}_((-(-(a&(-a))))>(-(a>(-(-a)))))
{}_((a>(-(-a)))>(-(a&(-a))))
{}_(a>(-(-a)))
{}_(-(a&(-a)))

next_theorem # T7

{(a|b)}_((a|b)>((-a)>b))
{(a|b)}_(a|b)
{(a|b)}_((-a)>b)
{(a|b)}_(b>(-(-b)))
{(a|b)}_((-a)>(-(-b)))
{(a|b)}_(((-a)>(-(-b)))>((-b)>a))
{(a|b)}_((-b)>a)
{(a|b)}_(((-b)>a)>(b|a))
{(a|b)}_(b|a)
{}_((a|b)>(b|a))

next_theorem # T8

{a}_(a>((-b)>a))
{a}_a
{a}_((-b)>a)
{a}_(((-b)>a)>(b|a))
{a}_(b|a)
{}_(a>(b|a))

next_theorem # T9

{}_(a>(b|a))
{}_((b|a)>(a|b))
{}_(a>(a|b))

next_theorem # T10

{(a>(-b))}_((-(-a))>a)
{(a>(-b))}_(((-(-a))>(a>(-b)))>(((-(-a))>a)>((-(-a))>(-b))))
{(a>(-b))}_((a>(-b))>((-(-a))>(a>(-b))))
{(a>(-b))}_(a>(-b))
{(a>(-b))}_((-(-a))>(a>(-b)))
{(a>(-b))}_(((-(-a))>a)>((-(-a))>(-b)))
{(a>(-b))}_((-(-a))>(-b))
{(a>(-b))}_(((-(-a))>(-b))>(b>(-a)))
{(a>(-b))}_(b>(-a))
{}_((a>(-b))>(b>(-a)))

next_theorem # T11

{}_((a&b)>(-(a>(-b))))
{}_((b>(-a))>(a>(-b)))
{}_((a>(-b))>(-(-(a>(-b)))))
{}_((b>(-a))>(-(-(a>(-b)))))
{}_(((b>(-a))>(-(-(a>(-b)))))>((-(a>(-b)))>(-(b>(-a)))))
{}_((-(a>(-b)))>(-(b>(-a))))
{}_((-(b>(-a)))>(b&a))
{}_((-(a>(-b)))>(b&a))
{}_((a&b)>(b&a))

next_theorem # T12

{}_((-b)>(a>(-b)))
{}_((a>(-b))>(-(-(a>(-b)))))
{}_((-b)>(-(-(a>(-b)))))
{}_(((-b)>(-(-(a>(-b)))))>((-(a>(-b)))>b))
{}_((-(a>(-b)))>b)
{}_((a&b)>(-(a>(-b))))
{}_((a&b)>b)

next_theorem # T13

{}_((a&b)>(b&a))
{}_((b&a)>a)
{}_((a&b)>a)

next_theorem # T14

{a, b}_((a>(-b))>(a>(-b)))
{a, b}_(a>((a>(-b))>a))
{a, b}_a
{a, b}_((a>(-b))>a)
{a, b}_(((a>(-b))>(a>(-b)))>(((a>(-b))>a)>((a>(-b))>(-b))))
{a, b}_(((a>(-b))>a)>((a>(-b))>(-b)))
{a, b}_((a>(-b))>(-b))
{a, b}_(((a>(-b))>(-b))>(b>(-(a>(-b)))))
{a, b}_(b>(-(a>(-b))))
{a, b}_b
{a, b}_(-(a>(-b)))
{a, b}_((-(a>(-b)))>(a&b))
{a, b}_(a&b)

next_theorem # T15

{((a&b)&c)}_(((a&b)&c)>(a&b))
{((a&b)&c)}_(((a&b)&c)>c)
{((a&b)&c)}_((a&b)&c)
{((a&b)&c)}_(a&b)
{((a&b)&c)}_c
{((a&b)&c)}_((a&b)>a)
{((a&b)&c)}_((a&b)>b)
{((a&b)&c)}_a
{((a&b)&c)}_b
{((a&b)&c)}_(b&c)
{((a&b)&c)}_(a&(b&c))
{}_(((a&b)&c)>(a&(b&c)))

next_theorem # T16

{(a&(b&c))}_((a&(b&c))>(b&c))
{(a&(b&c))}_((a&(b&c))>a)
{(a&(b&c))}_(a&(b&c))
{(a&(b&c))}_(b&c)
{(a&(b&c))}_a
{(a&(b&c))}_((b&c)>b)
{(a&(b&c))}_((b&c)>c)
{(a&(b&c))}_b
{(a&(b&c))}_c
{(a&(b&c))}_(a&b)
{(a&(b&c))}_((a&b)&c)
{}_((a&(b&c))>((a&b)&c))

next_theorem # T17

{(a>b)}_(((-(-a))>(-(-b)))>((-b)>(-a)))
{(a>b)}_((-(-a))>a)
{(a>b)}_(a>b)
{(a>b)}_(b>(-(-b)))
{(a>b)}_((-(-a))>b)
{(a>b)}_((-(-a))>(-(-b)))
{(a>b)}_((-b)>(-a))
{}_((a>b)>((-b)>(-a)))

next_theorem # T18

{(a>(-b))}_((-(-a))>a)
{(a>(-b))}_(a>(-b))
{(a>(-b))}_((-(-a))>(-b))
{}_((a>(-b))>((-(-a))>(-b)))
{}_((-(-(a>(-b))))>(a>(-b)))
{}_((-(-(a>(-b))))>((-(-a))>(-b)))
{}_(((-(a>(-b)))>(a&b))>((-(a&b))>(-(-(a>(-b))))))
{}_((-(a>(-b)))>(a&b))
{}_((-(a&b))>(-(-(a>(-b)))))
{}_((-(a&b))>((-(-a))>(-b)))
{}_(((-(-a))>(-b))>((-a)|(-b)))
{}_((-(a&b))>((-a)|(-b)))

next_theorem # T19

{}_(((-a)>b)>(a|b))
{}_((((-a)>b)>(a|b))>((-(a|b))>(-((-a)>b))))
{}_((-(a|b))>(-((-a)>b)))
{}_(((-(-b))>b)>((-a)>((-(-b))>b)))
{}_((-(-b))>b)
{}_((-a)>((-(-b))>b))
{}_(((-a)>((-(-b))>b))>(((-a)>(-(-b)))>((-a)>b)))
{}_(((-a)>(-(-b)))>((-a)>b))
{}_((((-a)>(-(-b)))>((-a)>b))>((-((-a)>b))>(-((-a)>(-(-b))))))
{}_((-((-a)>b))>(-((-a)>(-(-b)))))
{}_((-((-a)>(-(-b))))>((-a)&(-b)))
{}_((-((-a)>b))>((-a)&(-b)))
{}_((-(a|b))>((-a)&(-b)))

next_theorem # T20

{(a|b), (a>c), (b>c)}_((a|b)>((-a)>b))
{(a|b), (a>c), (b>c)}_(a|b)
{(a|b), (a>c), (b>c)}_((-a)>b)
{(a|b), (a>c), (b>c)}_(b>c)
{(a|b), (a>c), (b>c)}_((-a)>c)
{(a|b), (a>c), (b>c)}_(a>c)
{(a|b), (a>c), (b>c)}_((a>c)>((-c)>(-a)))
{(a|b), (a>c), (b>c)}_((-c)>(-a))
{(a|b), (a>c), (b>c)}_(((-a)>c)>((-c)>(-(-a))))
{(a|b), (a>c), (b>c)}_((-c)>(-(-a)))
{(a|b), (a>c), (b>c)}_((-(-a))>a)
{(a|b), (a>c), (b>c)}_((-c)>a)
{(a|b), (a>c), (b>c)}_(((-c)>(-a))>(((-c)>a)>c))
{(a|b), (a>c), (b>c)}_(((-c)>a)>c)
{(a|b), (a>c), (b>c)}_c

next_theorem # T21

{((-a)>b)}_((-a)>b)
{((-a)>b)}_(b>(-(-b)))
{((-a)>b)}_((-a)>(-(-b)))
{}_(((-a)>b)>((-a)>(-(-b))))
{((-a)&(-b))}_(((-a)>b)>((-a)>(-(-b))))
{((-a)&(-b))}_(((-a)&(-b))>(-((-a)>(-(-b)))))
{((-a)&(-b))}_((-a)&(-b))
{((-a)&(-b))}_(-((-a)>(-(-b))))
{((-a)&(-b))}_((((-a)>b)>((-a)>(-(-b))))>((-((-a)>(-(-b))))>(-((-a)>b))))
{((-a)&(-b))}_((-((-a)>(-(-b))))>(-((-a)>b)))
{((-a)&(-b))}_(-((-a)>b))
{((-a)&(-b))}_((a|b)>((-a)>b))
{((-a)&(-b))}_(((a|b)>((-a)>b))>((-((-a)>b))>(-(a|b))))
{((-a)&(-b))}_((-((-a)>b))>(-(a|b)))
{((-a)&(-b))}_(-(a|b))
{}_(((-a)&(-b))>(-(a|b)))

next_theorem # T22

{((-a)|(-b))}_((-a)|(-b))
{((-a)|(-b))}_((a&b)>a)
{((-a)|(-b))}_((a&b)>b)
{((-a)|(-b))}_(((a&b)>a)>((-a)>(-(a&b))))
{((-a)|(-b))}_(((a&b)>b)>((-b)>(-(a&b))))
{((-a)|(-b))}_((-a)>(-(a&b)))
{((-a)|(-b))}_((-b)>(-(a&b)))
{((-a)|(-b))}_(-(a&b))
{}_(((-a)|(-b))>(-(a&b)))

next_theorem # T23

{((-a)>(b|c)), (-(a|b))}_((-(a|b))>((-a)&(-b)))
{((-a)>(b|c)), (-(a|b))}_(-(a|b))
{((-a)>(b|c)), (-(a|b))}_((-a)&(-b))
{((-a)>(b|c)), (-(a|b))}_(((-a)&(-b))>(-a))
{((-a)>(b|c)), (-(a|b))}_(((-a)&(-b))>(-b))
{((-a)>(b|c)), (-(a|b))}_(-a)
{((-a)>(b|c)), (-(a|b))}_(-b)
{((-a)>(b|c)), (-(a|b))}_((-a)>(b|c))
{((-a)>(b|c)), (-(a|b))}_(b|c)
{((-a)>(b|c)), (-(a|b))}_((b|c)>((-b)>c))
{((-a)>(b|c)), (-(a|b))}_((-b)>c)
{((-a)>(b|c)), (-(a|b))}_c
{((-a)>(b|c))}_((-(a|b))>c)
{}_(((-a)>(b|c))>((-(a|b))>c))
{}_((a|(b|c))>((-a)>(b|c)))
{}_(((-(a|b))>c)>((a|b)|c))
{}_((a|(b|c))>((-(a|b))>c))
{}_((a|(b|c))>((a|b)|c))

next_theorem # T24

{((a|b)|c)}_(((a|b)|c)>(c|(a|b)))
{((a|b)|c)}_((c|(a|b))>((c|a)|b))
{((a|b)|c)}_(((c|a)|b)>(b|(c|a)))
{((a|b)|c)}_((b|(c|a))>((b|c)|a))
{((a|b)|c)}_(((b|c)|a)>(a|(b|c)))
{((a|b)|c)}_((a|b)|c)
{((a|b)|c)}_(c|(a|b))
{((a|b)|c)}_((c|a)|b)
{((a|b)|c)}_(b|(c|a))
{((a|b)|c)}_((b|c)|a)
{((a|b)|c)}_(a|(b|c))
{}_(((a|b)|c)>(a|(b|c)))

next_theorem # T25

{(a|(b&c))}_((a|(b&c))>((-a)>(b&c)))
{(a|(b&c))}_(a|(b&c))
{(a|(b&c))}_((-a)>(b&c))
{(a|(b&c))}_((b&c)>b)
{(a|(b&c))}_((b&c)>c)
{(a|(b&c))}_((-a)>b)
{(a|(b&c))}_((-a)>c)
{(a|(b&c))}_(((-a)>b)>(a|b))
{(a|(b&c))}_(((-a)>c)>(a|c))
{(a|(b&c))}_(a|b)
{(a|(b&c))}_(a|c)
{(a|(b&c))}_((a|b)&(a|c))
{}_((a|(b&c))>((a|b)&(a|c)))

next_theorem # T26

{(a&(b|c)), (-(-(a>(-b))))}_(a&(b|c))
{(a&(b|c)), (-(-(a>(-b))))}_((a&(b|c))>a)
{(a&(b|c)), (-(-(a>(-b))))}_((a&(b|c))>(b|c))
{(a&(b|c)), (-(-(a>(-b))))}_a
{(a&(b|c)), (-(-(a>(-b))))}_(b|c)
{(a&(b|c)), (-(-(a>(-b))))}_((b|c)>((-b)>c))
{(a&(b|c)), (-(-(a>(-b))))}_((-b)>c)
{(a&(b|c)), (-(-(a>(-b))))}_((-(-(a>(-b))))>(a>(-b)))
{(a&(b|c)), (-(-(a>(-b))))}_(-(-(a>(-b))))
{(a&(b|c)), (-(-(a>(-b))))}_(a>(-b))
{(a&(b|c)), (-(-(a>(-b))))}_(-b)
{(a&(b|c)), (-(-(a>(-b))))}_c
{(a&(b|c)), (-(-(a>(-b))))}_(a&c)
{(a&(b|c))}_((-(-(a>(-b))))>(a&c))
{}_((a&(b|c))>((-(-(a>(-b))))>(a&c)))
{(a&(b|c))}_((a&(b|c))>((-(-(a>(-b))))>(a&c)))
{(a&(b|c))}_(a&(b|c))
{(a&(b|c))}_((-(-(a>(-b))))>(a&c))
{(a&(b|c))}_((-(a>(-b)))>(a&b))
{(a&(b|c))}_(((-(a>(-b)))>(a&b))>((-(a&b))>(-(-(a>(-b))))))
{(a&(b|c))}_((-(a&b))>(-(-(a>(-b)))))
{(a&(b|c))}_((-(a&b))>(a&c))
{(a&(b|c))}_(((-(a&b))>(a&c))>((a&b)|(a&c)))
{(a&(b|c))}_((a&b)|(a&c))
{}_((a&(b|c))>((a&b)|(a&c)))

next_theorem # T27

{((a|b)&(a|c)), (-a)}_(((a|b)&(a|c))>(a|b))
{((a|b)&(a|c)), (-a)}_(((a|b)&(a|c))>(a|c))
{((a|b)&(a|c)), (-a)}_((a|b)&(a|c))
{((a|b)&(a|c)), (-a)}_(a|b)
{((a|b)&(a|c)), (-a)}_(a|c)
{((a|b)&(a|c)), (-a)}_((a|b)>((-a)>b))
{((a|b)&(a|c)), (-a)}_((a|c)>((-a)>c))
{((a|b)&(a|c)), (-a)}_((-a)>b)
{((a|b)&(a|c)), (-a)}_((-a)>c)
{((a|b)&(a|c)), (-a)}_(-a)
{((a|b)&(a|c)), (-a)}_b
{((a|b)&(a|c)), (-a)}_c
{((a|b)&(a|c)), (-a)}_(b&c)
{((a|b)&(a|c))}_((-a)>(b&c))
{((a|b)&(a|c))}_(((-a)>(b&c))>(a|(b&c)))
{((a|b)&(a|c))}_(a|(b&c))
{}_(((a|b)&(a|c))>(a|(b&c)))

next_theorem # T28

{((a&b)|(a&c))}_(((a&b)|(a&c))>((-(a&b))>(a&c)))
{((a&b)|(a&c))}_((a&b)|(a&c))
{((a&b)|(a&c))}_((-(a&b))>(a&c))
{((a&b)|(a&c))}_((a&b)|(-(a&b)))
{((a&b)|(a&c))}_((a&b)>a)
{((a&b)|(a&c))}_((a&c)>a)
{((a&b)|(a&c))}_((-(a&b))>a)
{((a&b)|(a&c))}_a
{((a&b)|(a&c))}_((a&b)>b)
{((a&b)|(a&c))}_(b>(b|c))
{((a&b)|(a&c))}_((a&b)>(b|c))
{((a&b)|(a&c))}_((a&c)>c)
{((a&b)|(a&c))}_(c>(b|c))
{((a&b)|(a&c))}_((a&c)>(b|c))
{((a&b)|(a&c))}_((-(a&b))>(b|c))
{((a&b)|(a&c))}_(b|c)
{((a&b)|(a&c))}_(a&(b|c))
{}_(((a&b)|(a&c))>(a&(b|c)))

next_theorem # T29

{(a>b), (b>a)}_(a>b)
{(a>b), (b>a)}_(b>a)
{(a>b), (b>a)}_((a>b)&(b>a))
{(a>b), (b>a)}_(((a>b)&(b>a))>(a~b))
{(a>b), (b>a)}_(a~b)

next_theorem # T30

{}_(a>(-(-a)))
{}_((-(-a))>a)
{}_(a~(-(-a)))

next_theorem # T31

{}_((a>b)>((-b)>(-a)))
{}_(((-b)>(-a))>(a>b))
{}_((a>b)~((-b)>(-a)))

next_theorem # T32

{}_((a|b)>(b|a))
{}_((b|a)>(a|b))
{}_((a|b)~(b|a))

next_theorem # T33

{}_((a&b)>(b&a))
{}_((b&a)>(a&b))
{}_((a&b)~(b&a))

next_theorem # T34

{}_(((a&b)&c)>(a&(b&c)))
{}_((a&(b&c))>((a&b)&c))
{}_(((a&b)&c)~(a&(b&c)))

next_theorem # T35

{}_(((a|b)|c)>(a|(b|c)))
{}_((a|(b|c))>((a|b)|c))
{}_(((a|b)|c)~(a|(b|c)))

next_theorem # T36

{}_((-(a&b))>((-a)|(-b)))
{}_(((-a)|(-b))>(-(a&b)))
{}_((-(a&b))~((-a)|(-b)))

next_theorem # T37

{}_((-(a|b))>((-a)&(-b)))
{}_(((-a)&(-b))>(-(a|b)))
{}_((-(a|b))~((-a)&(-b)))

next_theorem # T38

{}_((a|(b&c))>((a|b)&(a|c)))
{}_(((a|b)&(a|c))>(a|(b&c)))
{}_((a|(b&c))~((a|b)&(a|c)))

next_theorem # T39

{}_((a&(b|c))>((a&b)|(a&c)))
{}_(((a&b)|(a&c))>(a&(b|c)))
{}_((a&(b|c))~((a&b)|(a&c)))

next_theorem # T40

{}_((a~b)>((a>b)&(b>a)))
{}_(((a>b)&(b>a))>((b>a)&(a>b)))
{}_(((b>a)&(a>b))>(b~a))
{}_((b~a)>((b>a)&(a>b)))
{}_(((b>a)&(a>b))>((a>b)&(b>a)))
{}_(((a>b)&(b>a))>(a~b))
{}_((a~b)>((b>a)&(a>b)))
{}_((a~b)>(b~a))
{}_((b~a)>((a>b)&(b>a)))
{}_((b~a)>(a~b))
{}_(((a~b)>(b~a))&((b~a)>(a~b)))
{}_((((a~b)>(b~a))&((b~a)>(a~b)))>((a~b)~(b~a)))
{}_((a~b)~(b~a))
"""

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

estring = """
############## T0

A2[a=a, b=(a>a), c=a]
A1[a=a, b=(a>a)]
A1[a=a, b=a]
MP[0, 1]
MP[3, 2]

next_theorem # T1

HYP
A1[a=(-(-a)), b=(-a)]
MP[1, 0]
A3[a=a, b=(-a)]
MP[3, 2]
T0[a=(-a)][]
MN[5]
MP[4, 6]
DT[7]

next_theorem # T2

A5[a=a, b=(-a)]
T0[a=(-a)][]
MP[0, 1]

next_theorem # T3

A3[a=(-(-a)), b=a]
T1[a=(-a)][]
MP[0, 1]
A1[a=a, b=(-(-(-a)))]
HYP
MP[3, 4]
MP[2, 5]
DT[6]

next_theorem # T4

A3[a=a, b=b]
HYP
MP[0, 1]
A1[a=b, b=(-a)]
HYP
MP[3, 4]
MP[2, 5]
DT[6]
DT[7]

next_theorem # T5

HYP
HYP
A2[a=a, b=b, c=c]
A1[a=(b>c), b=a]
MP[3, 1]
MP[2, 4]
MP[5, 0]

next_theorem # T6

T4[a=(-(a&(-a))), b=(a>(-(-a)))][]
T1[a=(a&(-a))][]
A6[a=a, b=(-a)]
T5[a=(-(-(a&(-a)))), b=(a&(-a)), c=(-(a>(-(-a))))][1, 2]
MP[0, 3]
T3[a=a][]
MP[4, 5]

next_theorem # T7

A4[a=a, b=b]
HYP
MP[0, 1]
T3[a=b][]
T5[a=(-a), b=b, c=(-(-b))][2, 3]
T4[a=a, b=(-b)][]
MP[5, 4]
A5[a=b, b=a]
MP[7, 6]
DT[8]

next_theorem # T8

A1[a=a, b=(-b)]
HYP
MP[0, 1]
A5[a=b, b=a]
MP[3, 2]
DT[4]

next_theorem # T9

T8[a=a, b=b][]
T7[a=b, b=a][]
T5[a=a, b=(b|a), c=(a|b)][0, 1]

next_theorem # T10

T1[a=a][]
A2[a=(-(-a)), b=a, c=(-b)]
A1[a=(a>(-b)), b=(-(-a))]
HYP
MP[2, 3]
MP[1, 4]
MP[5, 0]
T4[a=(-a), b=b][]
MP[7, 6]
DT[8]

next_theorem # T11

A6[a=a, b=b]
T10[a=b, b=a][]
T3[a=(a>(-b))][]
T5[a=(b>(-a)), b=(a>(-b)), c=(-(-(a>(-b))))][1, 2]
T10[a=(b>(-a)), b=(-(a>(-b)))][]
MP[4, 3]
A7[a=b, b=a]
T5[a=(-(a>(-b))), b=(-(b>(-a))), c=(b&a)][5, 6]
T5[a=(a&b), b=(-(a>(-b))), c=(b&a)][0, 7]

next_theorem # T12

A1[a=(-b), b=a]
T3[a=(a>(-b))][]
T5[a=(-b), b=(a>(-b)), c=(-(-(a>(-b))))][0, 1]
T4[a=b, b=(-(a>(-b)))][]
MP[3, 2]
A6[a=a, b=b]
T5[a=(a&b), b=(-(a>(-b))), c=b][5, 4]

next_theorem # T13

T11[a=a, b=b][]
T12[a=b, b=a][]
T5[a=(a&b), b=(b&a), c=a][0, 1]

next_theorem # T14

T0[a=(a>(-b))][]
A1[a=a, b=(a>(-b))]
HYP
MP[1, 2]
A2[a=(a>(-b)), b=a, c=(-b)]
MP[4, 0]
MP[5, 3]
T10[a=(a>(-b)), b=b][]
MP[7, 6]
HYP
MP[8, 9]
A7[a=a, b=b]
MP[11, 10]

next_theorem # T15

T13[a=(a&b), b=c][]
T12[a=(a&b), b=c][]
HYP
MP[0, 2]
MP[1, 2]
T13[a=a, b=b][]
T12[a=a, b=b][]
MP[5, 3]
MP[6, 3]
T14[a=b, b=c][8, 4]
T14[a=a, b=(b&c)][7, 9]
DT[10]

next_theorem # T16

T12[a=a, b=(b&c)][]
T13[a=a, b=(b&c)][]
HYP
MP[0, 2]
MP[1, 2]
T13[a=b, b=c][]
T12[a=b, b=c][]
MP[5, 3]
MP[6, 3]
T14[a=a, b=b][4, 7]
T14[a=(a&b), b=c][9, 8]
DT[10]

next_theorem # T17

T4[a=(-a), b=(-b)][]
T1[a=a][]
HYP
T3[a=b][]
T5[a=(-(-a)), b=a, c=b][1, 2]
T5[a=(-(-a)), b=b, c=(-(-b))][4, 3]
MP[0, 5]
DT[6]

next_theorem # T18

T1[a=a][]
HYP
T5[a=(-(-a)), b=a, c=(-b)][0, 1]
DT[2]
T1[a=(a>(-b))][]
T5[a=(-(-(a>(-b)))), b=(a>(-b)), c=((-(-a))>(-b))][4, 3]
T17[a=(-(a>(-b))), b=(a&b)][]
A7[a=a, b=b]
MP[6, 7]
T5[a=(-(a&b)), b=(-(-(a>(-b)))), c=((-(-a))>(-b))][8, 5]
A5[a=(-a), b=(-b)]
T5[a=(-(a&b)), b=((-(-a))>(-b)), c=((-a)|(-b))][9, 10]

next_theorem # T19

A5[a=a, b=b]
T17[a=((-a)>b), b=(a|b)][]
MP[1, 0]
A1[a=((-(-b))>b), b=(-a)]
T1[a=b][]
MP[3, 4]
A2[a=(-a), b=(-(-b)), c=b]
MP[6, 5]
T17[a=((-a)>(-(-b))), b=((-a)>b)][]
MP[8, 7]
A7[a=(-a), b=(-b)]
T5[a=(-((-a)>b)), b=(-((-a)>(-(-b)))), c=((-a)&(-b))][9, 10]
T5[a=(-(a|b)), b=(-((-a)>b)), c=((-a)&(-b))][2, 11]

next_theorem # T20

A4[a=a, b=b]
HYP
MP[0, 1]
HYP
T5[a=(-a), b=b, c=c][2, 3]
HYP
T17[a=a, b=c][]
MP[6, 5]
T17[a=(-a), b=c][]
MP[8, 4]
T1[a=a][]
T5[a=(-c), b=(-(-a)), c=a][9, 10]
A3[a=c, b=a]
MP[12, 7]
MP[13, 11]

next_theorem # T21

HYP
T3[a=b][]
T5[a=(-a), b=b, c=(-(-b))][0, 1]
DT[2]
MN[3]
A6[a=(-a), b=(-b)]
HYP
MP[5, 6]
T17[a=((-a)>b), b=((-a)>(-(-b)))][]
MP[8, 4]
MP[9, 7]
A4[a=a, b=b]
T17[a=(a|b), b=((-a)>b)][]
MP[12, 11]
MP[13, 10]
DT[14]

next_theorem # T22

HYP
T13[a=a, b=b][]
T12[a=a, b=b][]
T17[a=(a&b), b=a][]
T17[a=(a&b), b=b][]
MP[3, 1]
MP[4, 2]
T20[a=(-a), b=(-b), c=(-(a&b))][0, 5, 6]
DT[7]

next_theorem # T23

T19[a=a, b=b][]
HYP
MP[0, 1]
T13[a=(-a), b=(-b)][]
T12[a=(-a), b=(-b)][]
MP[3, 2]
MP[4, 2]
HYP
MP[7, 5]
A4[a=b, b=c]
MP[9, 8]
MP[10, 6]
DT[11]
DT[12]
A4[a=a, b=(b|c)]
A5[a=(a|b), b=c]
T5[a=(a|(b|c)), b=((-a)>(b|c)), c=((-(a|b))>c)][14, 13]
T5[a=(a|(b|c)), b=((-(a|b))>c), c=((a|b)|c)][16, 15]

next_theorem # T24

T7[a=(a|b), b=c][]
T23[a=c, b=a, c=b][]
T7[a=(c|a), b=b][]
T23[a=b, b=c, c=a][]
T7[a=(b|c), b=a][]
HYP
MP[0, 5]
MP[1, 6]
MP[2, 7]
MP[3, 8]
MP[4, 9]
DT[10]

next_theorem # T25

A4[a=a, b=(b&c)]
HYP
MP[0, 1]
T13[a=b, b=c][]
T12[a=b, b=c][]
T5[a=(-a), b=(b&c), c=b][2, 3]
T5[a=(-a), b=(b&c), c=c][2, 4]
A5[a=a, b=b]
A5[a=a, b=c]
MP[7, 5]
MP[8, 6]
T14[a=(a|b), b=(a|c)][9, 10]
DT[11]

next_theorem # T26

HYP
T13[a=a, b=(b|c)][]
T12[a=a, b=(b|c)][]
MP[1, 0]
MP[2, 0]
A4[a=b, b=c]
MP[5, 4]
T1[a=(a>(-b))][]
HYP
MP[7, 8]
MP[9, 3]
MP[6, 10]
T14[a=a, b=c][3, 11]
DT[12]
DT[13]
MN[14]
HYP
MP[15, 16]
A7[a=a, b=b]
T17[a=(-(a>(-b))), b=(a&b)][]
MP[19, 18]
T5[a=(-(a&b)), b=(-(-(a>(-b)))), c=(a&c)][20, 17]
A5[a=(a&b), b=(a&c)]
MP[22, 21]
DT[23]

next_theorem # T27

T13[a=(a|b), b=(a|c)][]
T12[a=(a|b), b=(a|c)][]
HYP
MP[0, 2]
MP[1, 2]
A4[a=a, b=b]
A4[a=a, b=c]
MP[5, 3]
MP[6, 4]
HYP
MP[7, 9]
MP[8, 9]
T14[a=b, b=c][10, 11]
DT[12]
A5[a=a, b=(b&c)]
MP[14, 13]
DT[15]

next_theorem # T28

A4[a=(a&b), b=(a&c)]
HYP
MP[0, 1]
T2[a=(a&b)][]
T13[a=a, b=b][]
T13[a=a, b=c][]
T5[a=(-(a&b)), b=(a&c), c=a][2, 5]
T20[a=(a&b), b=(-(a&b)), c=a][3, 4, 6]
T12[a=a, b=b][]
T9[a=b, b=c][]
T5[a=(a&b), b=b, c=(b|c)][8, 9]
T12[a=a, b=c][]
T8[a=c, b=b][]
T5[a=(a&c), b=c, c=(b|c)][11, 12]
T5[a=(-(a&b)), b=(a&c), c=(b|c)][2, 13]
T20[a=(a&b), b=(-(a&b)), c=(b|c)][3, 10, 14]
T14[a=a, b=(b|c)][7, 15]
DT[16]

next_theorem # T29

HYP
HYP
T14[a=(a>b), b=(b>a)][0, 1]
A9[a=a, b=b]
MP[3, 2]

next_theorem # T30

T3[a=a][]
T1[a=a][]
T29[a=a, b=(-(-a))][0, 1]

next_theorem # T31

T17[a=a, b=b][]
T4[a=b, b=a][]
T29[a=(a>b), b=((-b)>(-a))][0, 1]

next_theorem # T32

T7[a=a, b=b][]
T7[a=b, b=a][]
T29[a=(a|b), b=(b|a)][0, 1]

next_theorem # T33

T11[a=a, b=b][]
T11[a=b, b=a][]
T29[a=(a&b), b=(b&a)][0, 1]

next_theorem # T34

T15[a=a, b=b, c=c][]
T16[a=a, b=b, c=c][]
T29[a=((a&b)&c), b=(a&(b&c))][0, 1]

next_theorem # T35

T24[a=a, b=b, c=c][]
T23[a=a, b=b, c=c][]
T29[a=((a|b)|c), b=(a|(b|c))][0, 1]

next_theorem # T36

T18[a=a, b=b][]
T22[a=a, b=b][]
T29[a=(-(a&b)), b=((-a)|(-b))][0, 1]

next_theorem # T37

T19[a=a, b=b][]
T21[a=a, b=b][]
T29[a=(-(a|b)), b=((-a)&(-b))][0, 1]

next_theorem # T38

T25[a=a, b=b, c=c][]
T27[a=a, b=b, c=c][]
T29[a=(a|(b&c)), b=((a|b)&(a|c))][0, 1]

next_theorem # T38

T26[a=a, b=b, c=c][]
T28[a=a, b=b, c=c][]
T29[a=(a&(b|c)), b=((a&b)|(a&c))][0, 1]

next_theorem # T40

A8[a=a, b=b]
T11[a=(a>b), b=(b>a)][]
A9[a=b, b=a]
A8[a=b, b=a]
T11[a=(b>a), b=(a>b)][]
A9[a=a, b=b]
T5[a=(a~b), b=((a>b)&(b>a)), c=((b>a)&(a>b))][0, 1]
T5[a=(a~b), b=((b>a)&(a>b)), c=(b~a)][6, 2]
T5[a=(b~a), b=((b>a)&(a>b)), c=((a>b)&(b>a))][3, 4]
T5[a=(b~a), b=((a>b)&(b>a)), c=(a~b)][8, 5]
T14[a=((a~b)>(b~a)), b=((b~a)>(a~b))][7, 9]
A9[a=(a~b), b=(b~a)]
MP[11, 10]
"""

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

tstring = """
{}_(a>a)                       # T0:  ⊢ φ→φ
{}_((-(-a))>a)                 # T1:  ⊢ ¬¬φ→φ
{}_(a|(-a))                    # T2:  ⊢ φ∨¬φ
{}_(a>(-(-a)))                 # T3:  ⊢ φ→¬¬φ
{}_(((-a)>(-b))>(b>a))         # T4:  ⊢ (¬φ→¬χ)→(χ→φ)
{(a>b), (b>c)}_(a>c)           # T5:  {φ→χ, χ→ψ} ⊢ φ→ψ
{}_(-(a&(-a)))                 # T6:  ⊢ ¬(φ∧¬φ)
{}_((a|b)>(b|a))               # T7:  ⊢ (φ∨χ)→(χ∨φ)
{}_(a>(b|a))                   # T8:  ⊢ φ→(χ∨φ)
{}_(a>(a|b))                   # T9:  ⊢ φ→(φ∨χ)
{}_((a>(-b))>(b>(-a)))         # T10: ⊢ (φ→¬χ)→(χ→¬φ)
{}_((a&b)>(b&a))               # T11: ⊢ (φ∧χ)→(χ∧φ)
{}_((a&b)>b)                   # T12: ⊢ (φ∧χ)→χ
{}_((a&b)>a)                   # T13: ⊢ (φ∧χ)→φ
{a, b}_(a&b)                   # T14: {φ, χ} ⊢ φ∧χ
{}_(((a&b)&c)>(a&(b&c)))       # T15: ⊢ ((φ∧χ)∧ψ)→(φ∧(χ∧ψ))
{}_((a&(b&c))>((a&b)&c))       # T16: ⊢ (φ∧(χ∧ψ))→((φ∧χ)∧ψ)
{}_((a>b)>((-b)>(-a)))         # T17: ⊢ (φ→χ)→(¬χ→¬φ)
{}_((-(a&b))>((-a)|(-b)))      # T18: ⊢ ¬(φ∧χ)→(¬φ∨¬χ)
{}_((-(a|b))>((-a)&(-b)))      # T19: ⊢ ¬(φ∨χ)→(¬φ∧¬χ)
{(a|b), (a>c), (b>c)}_c        # T20: {φ∨χ, φ→ψ, χ→ψ} ⊢ χ
{}_(((-a)&(-b))>(-(a|b)))      # T21: ⊢ (¬φ∧¬χ)→¬(φ∨χ)
{}_(((-a)|(-b))>(-(a&b)))      # T22: ⊢ (¬φ∨¬χ)→¬(φ∧χ)
{}_((a|(b|c))>((a|b)|c))       # T23: ⊢ (φ∨(χ∨ψ))→((φ∨χ)∨ψ)
{}_(((a|b)|c)>(a|(b|c)))       # T24: ⊢ ((φ∨χ)∨ψ)→(φ∨(χ∨ψ))
{}_((a|(b&c))>((a|b)&(a|c)))   # T25: ⊢ (φ∨(χ∧ψ))→((φ∨χ)∧(φ∨ψ))
{}_((a&(b|c))>((a&b)|(a&c)))   # T26: ⊢ (φ∧(χ∨ψ))→((φ∨χ)∧(φ∨ψ))
{}_(((a|b)&(a|c))>(a|(b&c)))   # T27: ⊢ ((φ∨χ)∧(φ∨ψ))→(φ∨(χ∧ψ))
{}_(((a&b)|(a&c))>(a&(b|c)))   # T28: ⊢ ((φ∧χ)∨(φ∧ψ))→(φ∧(χ∨ψ))
{(a>b), (b>a)}_(a~b)           # T29: {φ→χ, χ→φ} ⊢ φ↔χ
{}_(a~(-(-a)))                 # T30: ⊢ φ↔¬¬φ
{}_((a>b)~((-b)>(-a)))         # T31: ⊢ (φ→χ)↔(¬χ→¬φ)
{}_((a|b)~(b|a))               # T32: ⊢ (φ∨χ)↔(χ∨φ)
{}_((a&b)~(b&a))               # T33: ⊢ (φ∧χ)↔(χ∧φ)
{}_(((a&b)&c)~(a&(b&c)))       # T34: ⊢ ((φ∧χ)∧ψ)↔(φ∧(χ∧ψ))
{}_(((a|b)|c)~(a|(b|c)))       # T35: ⊢ ((φ∨χ)∨ψ)↔(φ∨(χ∨ψ))
{}_((-(a&b))~((-a)|(-b)))      # T36: ⊢ ¬(φ∧χ)↔(¬φ∨¬χ)
{}_((-(a|b))~((-a)&(-b)))      # T37: ⊢ ¬(φ∨χ)↔(¬φ∧¬χ)
{}_((a|(b&c))~((a|b)&(a|c)))   # T38: ⊢ (φ∨(χ∧ψ))↔((φ∨χ)∧(φ∨ψ))
{}_((a&(b|c))~((a&b)|(a&c)))   # T39: ⊢ (φ∧(χ∨ψ))↔((φ∨χ)∧(φ∨ψ))
{}_((a~b)~(b~a))               # T40: ⊢ (φ↔χ)↔(χ↔φ)
"""

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
