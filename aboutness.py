import string

letters = list(string.ascii_uppercase)
numAtomic = 4

atomsList = letters[:numAtomic]

atomicDict ={atomsList[i] :i for i in range(len(atomsList))}
    
#atomicDict = {'A' : 0, 'B' :1 , 'C' :2, 'D' :3, 'E' : 4}

assignmentCode = {'T' : True, 'F': False, '-' : 'Neither', '*' : 'Both'}

negation = {'-', 'not', '~', 'Not', 'NOT'}
conjunction = {'&', 'and', 'And', 'AND'}
disjunction = {'v', 'or', 'OR', 'Or', '|'}
biconditional = {'iff', '<->', '<>'}
conditional = {'>', '->'}

operators = conjunction | negation | conditional | disjunction | biconditional


import qm
import inspect


def findatoms(sentence):
    """return the set of all atomic formulas in sentence"""
    if type(sentence) ==type('a'):
        return set(sentence)
    elif sentence[0] == '-' or sentence[0] == 'not':
        return findatoms(sentence[1])
    else:
        return findatoms(sentence[1][0])|findatoms(sentence[1][1])

def negate(sentence):
    """returns the negation of a sentence"""
    if isinstance(sentence, list):
        return ['-', sentence]
    else:
        return '-(' + sentence + ')'

    

def checkliteral(sentence):
    """returns true if sentence is a literal"""
    if isinstance(sentence, Fact):
        return False
    return type(sentence) ==type('a') or (sentence[0] in negation and type(sentence[1]) ==type('a'))
                                          
def makestring(sentence):
    """takes a literal sentence and returns a string (might be extended later)"""
    if checkliteral(sentence):
            if type(sentence) ==type('a'):
                return sentence
            else:
                return '-' + sentence[1]
    else:
            print('Not a literal! Need to write more code if want makeString to do general')


def makefact(sentence):
    """takes a literal sentence and returns a listfact"""
    assign = (blank_assignment())
    lassign = list(assign)
    if type(sentence) ==type('a'):
        lassign[atomicDict[sentence]]='1'
        listfact = ''
        for char in lassign:
            listfact = listfact +char
        return ''+ listfact
    else:
        lassign[atomicDict[sentence[1]]]='0'
        listfact = ''
        for char in lassign:
            listfact = listfact +char
        return '' + listfact
        


def makenegfact(sentence):
    """takes a literal sentence and returns a negative listfact (i.e. falsemaker)"""
    assign = blank_assignment()
    lassign = list(assign)
    if type(sentence) ==type('a'):
        lassign[atomicDict[sentence]]='0'
        listfact = ''
        for char in lassign:
            listfact = listfact +char
        return '' +listfact 
    else:
        
        lassign[atomicDict[sentence[1]]]='1'
        listfact = ''
        for char in lassign:
            listfact = listfact +char
        return '' + listfact





def ensure(sentence):
    """makes sure values is a parsed string"""
    if isinstance(sentence, str):
        return parse(sentence)
    else:
        return sentence





def parse(string):
    """returns a structured logical formula from string input, requires
    &,v,- as connectives.  does not respect order of operations generally but handles
    negations respectably"""
    old = string
    string = ""
    for i in range(len(old)):
        if old[i] != ' ':
            string = string + old[i]
    
    neg = False

    
    if len(string) == 0:
        return None
    oplen = getoplen(string)
    if oplen:
        string = string[oplen:]
        neg = True
    if len(string) == 1:
        if neg:
            return ['-', string]
        if not neg:
            return string  
    first = getfirst(string)
    if first == string:
        if not neg:
            return parse(string[1:len(string)-1])
        else:
            return ['-', parse(string[1:len(string)-1])]
    else:
        lenop = getoplen(string[len(first):])
        operator = string[len(first): len(first) + lenop]                     
        second = string[len(first)+lenop:]
        if neg:
            return [operator, [ [ '-', parse(first)] , parse(second)]]
        else:
            return [operator, [ parse(first), parse(second)]]

def getoplen(string):
    """returns the length of the operator heading a string"""
    for length in [3,2,1]:
        if len(string) > length:
            if string[:length] in operators:
                return length

    return False
    
    

    
def getfirst(string):
    """gets the first arugment of the string"""
    if string[0] in atomicDict:
        return string[0]
    if string[0] == '(':
        close = findclosep(string, 0)
        return string[0:close+1]
    else:
        return None
            
    
def findclosep(string, openp):
    """returns the position in string of the closing parenthesis for open at openp"""
    parcount = 0
    for i in range(openp, len(string)):
        if string[i] == '(':
            parcount = parcount +1
        elif string[i] == ')':
            parcount = parcount -1
        if parcount == 0:
            return i
    print('no closep! {}'.format(string))
    



    
        
def blank_assignment(num = numAtomic):
    """Returns an empty assignment string"""
    assign = ''
    for i in range(num):
        assign = assign + '-'
    return assign

def comb_assign(assign1, assign2):
    """combines two partial assignments"""
    assignnew = []
    for i in range(len(assign1)):
        values = set([assign1[i],assign2[i]])
        if len(values) == 1:
            assignnew.append(assign1[i])
        elif '1' in values and '0' in values:
            assignnew.append('*')
        elif '1' in values:
            assignnew.append('1')
        else:
            assignnew.append('0')
    return ''.join(assignnew)
            

def merge_assigns(assigns1, assigns2):
    """combines two lists of assignments, removing duplicates, returns result"""
    return list(set(assigns1 + assigns2))
    


def comb_assigns(assigns1, assigns2):
    """pairwise joining of assignments returns result"""
    assignsnew = []
    if len(assigns1) == 0:
        return assigns2
    if len(assigns2) == 0:
        return assigns1
    for i in range(len(assigns1)):
        for j in range(len(assigns2)):
            assignsnew.append(comb_assign(assigns1[i],assigns2[j]))
    return assignsnew


def van_truth(sentence):
    """return a set of the van Fraassen truthmakers of a wff"""
    sentence = ensure(sentence)
    assigns = []
    if isinstance(sentence, str):
        assigns.append(makefact(sentence))
    elif sentence[0] in negation:
        assigns = van_false(sentence[1])
    elif sentence[0] in conjunction:
        assigns = comb_assigns(van_truth(sentence[1][0]),van_truth(sentence[1][1]))
    elif sentence[0] in disjunction:
        assigns = merge_assigns(van_truth(sentence[1][0]),van_truth(sentence[1][1]))
    elif sentence[0] in conditional:
        assigns = merge_assigns(van_false(sentence[1][0]),van_truth(sentence[1][1]))
    elif sentence[0] in biconditional:
        assigns = comb_assigns(merge_assigns(van_false(sentence[1][0]),van_truth(sentence[1][1])), merge_assigns(van_false(sentence[1][1]),van_truth(sentence[1][0])))
    return assigns

        
        
    
    
    
    
    
 

def van_false(sentence):
    """return a set of hte van Fraassen falsemaker of a wff"""
    sentence = ensure(sentence)
    assigns = []
    if isinstance(sentence, str):
        assigns.append(makenegfact(sentence))
    elif sentence[0] in negation:
        assigns = van_truth(sentence[1])
    elif sentence[0] in conjunction:
        assigns = merge_assigns(van_false(sentence[1][0]),van_false(sentence[1][1]))
    elif sentence[0] in disjunction:
        assigns = comb_assigns(van_false(sentence[1][0]),van_false(sentence[1][1]))
    elif sentence[0] in conditional:
        assigns = comb_assigns(van_truth(sentence[1][0]),van_false(sentence[1][1]))
    elif sentence[0] in biconditional:
        assigns = merge_assigns(comb_assigns(van_truth(sentence[1][0]),van_false(sentence[1][1])), comb_assigns(van_truth(sentence[1][1]),van_false(sentence[1][0])))
    return assigns

def generate(poss = numAtomic):
    """returns a list of all possible truth value assignments for
    the atomc variables"""
    assignments = []
    for x in range(2**poss):
        if x == 0:
            assignments.append('0'*poss)
        else:
            binx = bin(x)[2:]
            filler = '0' * (poss - len(binx))
            assignment = filler + binx
            assignments.append(assignment) 
    return assignments

def evaluate(sentence, valuation):
    """Evalation sentence using list assignment of 1's and 0's"""
    sentence = ensure(sentence)
    value = False
    if type(sentence) ==type('a'):
        if  sentence == 'F' or sentence == 'T':
            return sentence == 'T'
        elif valuation[atomicDict[sentence]] == '0':
            return False
        else:
            return True
    if sentence[0] in negation:
        return not evaluate(sentence[1], valuation)
    if sentence[0] in conjunction:
        return evaluate(sentence[1][0], valuation) and evaluate(sentence[1][1], valuation)
    if sentence[0] in disjunction:
        return evaluate(sentence[1][0], valuation) or evaluate(sentence[1][1], valuation)
    if sentence[0] in conditional:
        return (not evaluate(sentence[1][0], valuation)) or evaluate(sentence[1][1], valuation)
    if sentence[0] in biconditional:
        return (evaluate(sentence[1][0], valuation)) is evaluate(sentence[1][1], valuation)
    return value

    
def findvaluations(sentence, assignments = generate()):
    """returns the list of all valuation in which a sentence is true"""
    sentence = ensure(sentence)
    trueassigns = []
    for i in range(len(assignments)):
        if evaluate(sentence, assignments[i]):
            trueassigns.append(assignments[i])
    return trueassigns



def findqm(sentence):
    """uses the Q=M algorithm to get the simplified truthmakers"""
    ensure(sentence)
    vals = findvaluations(sentence)
    if len(vals) == 0:
        return None
    qm1 = qm.QuineMcCluskey()
    vals = qm1.simplify_los(vals)
    if vals == None:
        return vals
    return list(vals)



def valtosent(valuation):
    """turn a valuation or list of valuation into a sentebnce"""
    if valuation == None:
        return ""
    if len(valuation) == 0:
        return 'F'
    if len(valuation) == 1 and valuation[0] == '-'*len(valuation[0]):
        return 'T'
    if type(valuation) == type([]):
        sentence = ""
        for k in range(len(valuation)):
            instance = valtosent(valuation[k])
            if len(instance) > 1:
                sentence= sentence+'v(' + instance + ')'
            else:
                sentence= sentence+'v' + instance 
        if sentence[0] == 'v':
            sentence = sentence[1:]
        return sentence    

    if isinstance(valuation, str):
        part = ""
        for i in range(len(valuation)):
            atom = list(atomicDict.keys())[list(atomicDict.values()).index(i)] ##using a dictionary backwards!
            if valuation[i] == '0':
                part = part +'&-' + atom
            if valuation[i] == '1':
                part = part +'&' + atom
            if valuation[i] == '*':
                part = part +'&' + atom + '&-' + atom
        if len(part)>= 1:
            part = part[1:]
        return part
    return ""


     

                   


def analyze(sentence):
    qmt = valtosent(findqm(sentence))
    qmf = valtosent(findqm(negate(sentence)))
    vft = valtosent(van_truth(sentence))
    vff = valtosent(van_false(sentence))
    print('Sentence = {}'.format(sentence))
    print('QM truthmaker = {}'.format(qmt))
    print('QM falsemaker = {}'.format(qmf))
    print('vF truthmaker = {}'.format(vft))
    print('vF falsemaker = {}'.format(vff))


def onpath(val1, val2, val3):
    """checks if val2 is on a path from val1 to val2"""
    for n in range(len(val2)):
        if val2[n] != val1[n] and val2[n] != val3[n]:
            return False
    return True


def minusval(sent1, sent2, valuation, mytype = 'S1'):
    """tells whether sent1 minus sent2
    is true at valuation"""
    if mytype == 'S1':
        if evaluate(sent1, valuation):
            return True
        tms_at_val = gen_tms(valuation)
        tms_con_sent2 = [x for x in tms_at_val if tm_comp_sent(x, sent2)]
        tms_final = [ x for x in tms_con_sent2 if tm_comb_sent_entail_sent(x, sent2, sent1)]
        if len(tms_final) == 0:
            return False
        else:
            return True
    if mytype == 'S2':
        if evaluate(sent1, valuation):
            return True
        tms_at_val = gen_tms(valuation)
        tms_sent2 = findqm(sent2)
        sent2s = map(valtosent, tms_sent2)
        for i in range(len(sent2s)):
            tms_con_sent2 = [x for x in tms_at_val if tm_comp_sent(x, sent2s[i])]
            tms_final = [ f for f in tms_con_sent2 if tm_comb_sent_entail_sent(f, sent2s[i], sent1)]
            if len(tms_final) > 0:
                return True
        return False
    if mytype == 'D4.1':
        tms1 = findqm(sent1)
        tms2 = findqm(negate(sent2))
        for tm1 in tms1:
            for tm2 in tms2:
                if tm_comp_sent(tm2, sent1):
                    if evaluate(sent1, valuation):
                        return True
                else:
                    weak = make_tm_consistent(tm1,tm2)
                    for k in weak:
                        if tm_at_world(valuation, k):
                            return True
                
    if mytype == 'D4.2':
        tms1 = findqm(sent1)
        tms2 = findqm(negate(sent2))
        for tm1 in tms1:
            for tm2 in tms2:
                weak = make_tm_consistent(tm1,tm2)
                for k in weak:
                    if tm_at_world(valuation, k):
                        return True

    if mytype == 'SIM':
        return evaluate( '(' + sent1 + ')' + 'v' + '-(' + sent2 + ')' , valuation)
    if mytype == 'S3WRONG':
        tms1 = findqm(sent1)
        tms2 = findqm(sent2)
        for tm1 in tms1:
            for tm2 in tms2:
                target = hashing(tm1,tm2)
                if tm_at_world(valuation, target):
                    return True
    if mytype == 'S3':
        tms1 = findqm(sent1)
        tms2 = findqm(sent2)
        for tm1 in tms1:
            for tm2 in tms2:
                target = hashing2(tm1,tm2)
                if tm_at_world(valuation, target):
                    return True
        return False
    if mytype == 'D-AGM':
        if evaluate(sent1, valuation):
            return True
        tms1 = findqm(sent1)
        tms2 = findqm(negate(sent2))
        isgood = False
        for tm1 in tms1:
            for tm2 in tms2:
                weak = make_tm_consistent(tm1,tm2)
                for k in weak:
                    if tm_at_world(valuation, k):
                        isgood = True
        if isgood:
            if evaluate('-('+ sent2+')', valuation):
                return True
        return False

    if mytype == 'SD':
        if evaluate(sent1, valuation):
            return True
        tms1 = findqm(sent1)
        tms2 = findqm(negate(sent2))
        for tm1 in tms1:
            for tm2 in tms2:
                if not tm_comp_sent(tm2, sent1):
                    target = carrot(tm1,tm2)
                    if tm_at_world(valuation, target):
                        return True
    


        
    
                        



def find_target(tm,sent):
    """returns set of targetted truthmakers from tm to sent"""
    vals_sent = findvaluations(sent)
    vals_sent = [val for val in vals_sent if tm_at_world(val, tm)]
    ttms = simplify_assignments(vals_sent)
    targets = []
    for ttm in ttms:
        newtm = ''
        for i in range(len(tm)):
            if tm[i] == '0' or tm[i] =='1':
                newtm = newtm + '-'
            else:
                newtm = newtm + ttm[i]
        targets.append(newtm)
    return targets
            
            
    
def carrot(tm1,tm2):
    target = ''
    for i in range(len(tm1)):
        if tm2[i] != tm1[i]:
            if tm2[i] == '-':
                target = target + tm1[i]
            elif tm1[i] == '-':
                target = target + tm2[i]
            else:
                target = target + '-'
        else:
            target = target + tm2[i]
    return target

            
def hashing(tm1,tm2):
    """implements Yablos function tm1#tm2 that gives you"""
    target = ''
    for i in range(len(tm2)):
        if tm2[i] != '-':
            target = target + '-'
        else:
            target = target + tm1[i]
    return target            

def hashing2(tm1,tm2):
    """implements Yablos ***ACTUAL*** function tm1#tm2 that gives you"""
    target = ''
    for i in range(len(tm2)):
        if tm1[i]!=tm2[i] or tm2 == '-':
            target = target + tm1[i]
        else:
            target = target + '-'
    return target            
                
                

                                              
        
        
        
     


def simplify_assignments(assigns):
    """runs the qm algorithm on a set of assignment to give a set of facts back"""
    qm1 = qm.QuineMcCluskey()
    assigns = qm1.simplify_los(assigns)
    if assigns == None:
        return[]
    return list(assigns)

def closer(w1, w2, w3):
    """returns true if w1 is strictly  closer to w3 as w2 is"""
    w1closer = False
    w2closer = False
    for n in range(len(w1)):
        if w1[n] == w3[n] and w2[n] != w3[n]:
            w1closer = True
        if w2[n] == w3[n] and w1[n] != w3[n]:
            w2closer = True
    return w1closer and not w2closer


def minus(sent1, sent2, mytype = 'SD'):
    """gives the qm form of the substraction of sent2 from sent1"""
    worlds = generate()
    if mytype == 'path':
        sworlds = [ w for w in worlds if minusval(sent1,sent2, w, 'D-AGM') ]
        s1worlds = findvaluations(sent1)
        s2worlds = findvaluations(sent2)
        targets = [w for w in sworlds if w not in s2worlds]
        #print('targets = {}'.format(valtosent(targets)))
        inbetween = [w for w in worlds if (w not in s1worlds and w in s2worlds)]
        #print('inbetween = {}'.format(valtosent(inbetween)))
        additions = [w for w in inbetween if len([(base, target) for base in s1worlds for target in targets if onpath(base, w, target)]) != 0]
        #print('additions = {}'.format(valtosent(additions)))
        sworlds = [w for w in worlds if w in sworlds or w in additions]
        return valtosent(simplify_assignments(sworlds))
    if mytype == 'short-path':
        #NB: not actually clear what this concept is!
        #print('hi')
        sworlds = [ w for w in worlds if minusval(sent1,sent2, w, 'D-AGM') ]
        s1worlds = findvaluations(sent1)
        s2worlds = findvaluations(sent2)
        inbetween = [w for w in worlds if (w not in s1worlds and w in s2worlds)]
        #print('inbetween = {}'.format(valtosent(inbetween)))
        targets = [w for w in sworlds if w not in s2worlds]
        additions =[]
        for target in targets:
            for start in s1worlds:
                if len([alt for alt in s1worlds if closer(alt, start, target)]) == 0:
                    #print('start {} target {}'.format(start, target))
                    
                    onroute = [w for w in inbetween if onpath(start, w, target)]
                    additions = additions + onroute                       
                inbetween = list(set(inbetween) - set(additions))
        #print('additions = {}'.format(valtosent(additions)))
        final = list(set([w for w in worlds if w in sworlds or w in additions]))
        return valtosent(simplify_assignments(final))

        
    worlds = [ w for w in worlds if minusval(sent1,sent2, w, mytype) ]
    return valtosent(simplify_assignments(worlds))
    


def might(sent1, sent2, mytype = 'SD'):
    """gives the qm form of the substraction of not sent2 from sent1"""
    sent2 = '-(' + sent2 +')'
    return minus(sent1, sent2, mytype)

def mightandnot(sent1, sent2, mytype = 'D4.2'):
    """adds might sent2 then subtracts sent 2"""
    inter = might(sent1,sent2, mytype)
    return valtosent(simplify_assignments(findvaluations('('+ inter +')' +'&-( ' +sent2+')'))) 
    
    




def tm_comb_sent_entail_sent(tm, sent1, sent2):
    """does tm combined with sent1 entail sent2"""
    tmvals = set(gen_vals(tm))
    sent1vals = set(findvaluations(sent1))
    sent2vals = set(findvaluations(sent2))
    if len((tmvals & sent1vals) - sent2vals) == 0:
        return True
    else:
        return False
        



def tm_comp_sent(tm, sent):
    """returns True if tm is compatible with sentence being true"""
    tmposs = set(gen_vals(tm))
    sentposs = set(findvaluations(sent))
    if len(tmposs & sentposs) == 0:
        return False
    else:
        return True
    
def tm_entail_sent(tm,sent):
    """returns true if tm entails sentence"""
    tmposs = set(gen_vals(tm))
    sentposs = set(findvaluations(sent))
    if len(tmposs - sentposs) == 0:
        return True
    else:
        return False
    
    
def tms_at_world(sent, valuation):
    """returns all the truthmakers of sent at valuation"""
    sent_tms = findqm(sent)
    return [x for x in sent_tms if tm_at_world(valuation, x)]
    

def gen_tms(valuation):
    """returns a list of all the truthmakers compatible with a valuation"""
    poss = generate(len(valuation))
    for i in range(len(poss)):
        assign = ""
        for j in range(len(poss[i])):
            if poss[i][j] == '1':
                assign = assign + '-'
            else:
                assign = assign + valuation[j]
        poss[i] = assign
    return poss

def gen_vals(tm):
    """returns a list of all valuations compatible with a tm"""
    poss = generate(len(tm))
    return [x for x in poss if tm_at_world(x,tm)] 



def tm_at_world(valuation, tm):
    """returns true of tm if true at valuation false otherwise"""
    for i in range(len(valuation)):
        if valuation[i] != tm[i] and tm[i] != '-' and tm[i] != '*':
            return False
    return True

            
def make_tm_consistent(tm1, sent):
    """returns list of least loosenings tm1 are sent consistent--can handle tms/vals as sent as well"""
    if sent[len(sent)-1] == '-' or sent[len(sent)-1] == '0' or sent[len(sent)-1] == '1':
        sent = valtosent(sent)
    poss_tms = list(set(gen_tms(tm1)))
    poss_tms = [f for f in poss_tms if tm_comp_sent(f, sent)]
    poss_tms = [f for f in poss_tms if len([g for g in poss_tms if more_precise(g,f)]) == 0] 
    return poss_tms

def more_precise(tm1,tm2):
    """returns true if tm1 is more precise than tm2"""
    val = False
    for i in range(len(tm1)):
        if tm1[i] != '-' and tm2[i] == '-':
            val = True
        else:
            if tm1[i] != tm2[i]:
                return False
    return val

    
        
kinds_subtraction = ['D4.2', 'SIM']
                   
sample_pairs = [['A&B','A'],['AvB', 'A'],['A&B&C', 'A&B'],['A&B', 'A&B'],['(A&B)v(C&D)','AvC']]
sample_pairs= [['A&B','A'],['AvB', 'A'],['A&B&C', 'A&B'],['A&B', 'A&B'],['(A&B)v(C&D)','AvC'],['A iff B', '-(A&-B)'],
               ['A&B', 'A iff B'], ['A&B', 'A&C'], ['AvB', 'A&C'],['A&(BvC)','AvB'], ['A', 'AvB'], ['A&B', 'AvB'],['(A&B)vC', 'AvB'],['A&B&C', 'AvB'] ] 



connectives = ['&', 'v', 'iff']
firstletters = ['A', '-A']
secondletters = ['B', '-B']

connectives2 = ['&', 'v']

threeset = ['(A' + x + 'B)' + y + 'C' for x in connectives2 for y in connectives2]
                 
firstset = [x+' '+y+' '+z for x in firstletters for y in connectives for z in secondletters]

secondset = ['A'] +firstset

sample_pairs2 =[ [x,y] for x in threeset for y in secondset]
sample_pairs1 =[ [x,y] for x in firstset for y in secondset ]
sample_pairs3= [[x,y] for x in threeset for y in threeset if x  != y]


part1 = might('(A&B)', '-B&-D', 'short-path')
part2 = might('(C&D)', '-B&-D', 'short-path')


test = might('(A&B)v(C&D)', '-B&-D', 'SD')

test2 = might('(A&B)v(C&D)', '-B&-D', 'short-path')

test3 = might('(A&B)v(C&D)', '-B&-D', 'D-AGM')

test4 = might('(-A&B)v(-B&C)', 'A&B', 'SD')


##
##for pair in sample_pairs1:
##    results =[]
##    for kind in kinds_subtraction:
##        results.append([kind, minus(pair[0] , pair[1], kind)])
##    if True: #results[0][1] != results[1][1]:
##        print('{} minus {}:'.format(pair[0] , pair[1]))
##        for result in results:
##            print(' {} says {}.'.format(result[0], result[1]),)
##        print('')
##
##
##
##

a = ('(A&B)v(A&-D)v(C&D)v(C&-B)')

t = range(27)

t[1] = ['A', '-A']
t[2] = ['A', 'B']
t[3] = ['A&B', '-A']
t[4] = ['A&B', '-(A&B)']
t[5] = ['A&B', '-(A iff B)']
t[6] = ['A&B', '-(A v B)']
t[7] = ['AvB', '-(A v B)']
t[8] = ['AvB', '-A']
t[9] = ['AvB', '-A v -C']
t[10] = ['A iff B', '-( A iff B)']
t[11] = ['A iff B', '-A']
t[12] = ['A iff B', '-(A > B)']
t[13] = ['A&B', '-(A iff B )']
t[14] = ['A&B', '-B&C']
t[15] = ['A&B', '-Bv-C']
t[16] = ['A & (B v C)' , '-A&-B']
t[17] = ['A & (B v C)' , '-Av-B']
t[18] = ['A & (B v C)' , '-B&-C']
t[19] = ['(A&B)vC', '-A&-B']
t[20] = ['(A&B)vC', '-A&-C']
t[21] = ['(A&B)vC', '-B&-C']
t[22] = ['(A&B)&C' , '-A&-B']
t[23] = ['(A&B)&C' , '(-B v (-A&-C))']
t[24]= ['(A&B)&C' , '(-Av-B v (-A&-C))']
t[25] = ['(A&B)v(C&D)', '-Av-B', 'SD']
t[26] = ['(A&B)v(C&D)', '-A&-C', 'SD']

def y_friend(formula):
    """Convert to a more steve friendly format by replacing 'A's and 'B's with 'p's and 'qs'"""
    ns = formula.replace('A', 'p')
    n2 = ns.replace('B', 'q')
    n3 = n2.replace('C', 'r')
    return n3.replace('D', 's')

for i in range(27):
    if i > 0:
        print('Row {}: {} <>{}  is {}'.format(i, y_friend(t[i][0]), y_friend(t[i][1]), y_friend(might(t[i][0],t[i][1]))))






