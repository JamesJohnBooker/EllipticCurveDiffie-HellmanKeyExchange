import math #This is needed to make use of Python's floor, ceiling and square root functions, for the purposes of computing the baby-step giant-step algorithm, which counts the number of elements in an elliptic curve over a finite field.
import random #This is needed for randomly generating and testing large primes, randomly generating the elliptic curve parameters a and b and randomly selecting points in the group Ep(a,b).



def generateKeys(p, a, xG, yG): #This function generates the private key integer `Nk' and private key point Mk = (`xMk', `yMk') for some user k.
    Nk = random.randint(1, p - 1) #User k's private key is some random integer from Zp.
    xMk, yMk = multiplyPoint(Nk, a, xG, yG, p) #User k's public key is the generator G = (`xG', `yG') multiplied by their private key `Nk'.
    return Nk, xMk, yMk 



def addDistinctPoints(xP, yP, xQ, yQ, p): #This function adds together two distinct points P = (`xP', `yP') and Q = (`xQ', `yQ') in the elliptic curve group Ep(a,b).
    gradient = (((yQ - yP) % p) * (modularExponentiation(xQ - xP, p - 2, p))) % p #This is the form of the gradient when adding two distinct points together, derived in the elliptic curve cryptography section of this project.
    xPaddQ = (((((gradient * gradient) % p) - xP) % p) - xQ) % p #The equation for the x coordinate of P + Q, as derived in the elliptic curve cryptography section earlier.
    yPaddQ = (((gradient * ((xP - xPaddQ) % p)) % p) - yP) % p #The equation for the y coordinate of P + Q, as derived in the elliptic curve cryptography section earlier.
    return xPaddQ, yPaddQ



def addIdenticalPoints(a, xP, yP, p): #This function adds a point P = (`xP', `yP') from the elliptic curve group Ep(a,b) to itself.
    gradient = (((((3 * modularExponentiation(xP, 2, p)) % p) + a) % p) * (modularExponentiation(2 * yP, p - 2, p))) % p #This is the form of the gradient when adding two identical points together, derived in the elliptic curve cryptography section of this project.
    xTwoP = (((gradient * gradient) % p) - ((2 * xP) % p)) % p #The equation for the x coordinate of 2P, as derived in the elliptic curve cryptography section earlier.
    yTwoP = (((gradient * ((xP - xTwoP) % p)) % p) - yP) % p #The equation for the y coordinate of 2P, as derived in the elliptic curve cryptography section earlier.
    return xTwoP, yTwoP



def multiplyPoint(k, a, xP, yP, p): #This function takes a point P = (`xP', `yP') from the elliptic curve group Ep(a,b) and computes the point kP = P + ... + P in the group, where P appears k times in the expression. This is the equivalent of the square-and-multiply algorithm for modular exponentiation but applied to the addition operation on points in Ep(a,b). The function can also reduce intermediate results modulo a prime `p' if desired, otherwise intermediate results will not be reduced if the parameter `p' is set to 0.
    l = 0
    xValue = 0
    yValue = 0
    xBase = xP
    yBase = yP
    while k > 0: #This while loop runs until kP has been computed.
        if k % 2 == 1: #If the current value of k is odd, `xValue' and `yValue' are increased.
            if l == 0: #The first time `xValue' and `yValue' are increased, they are simply set to the values of `xP' and `yP' respectively.
                xValue = xP
                yValue = yP
                l += 1
            elif xValue == xBase:
                if yValue == yBase: #If (`xValue', `yValue') = (`xBase', `yBase'), then they are the same point and so the formula for adding identical points is used.
                    xValue, yValue = addIdenticalPoints(a, xValue, yValue, p) #(`xValue', `yValue') is added to (`xValue', `yValue').
            else: #If (`xValue', `yValue') != (`xBase', `yBase'), then they are different points and so the formula for adding distinct points is used.
                xValue, yValue = addDistinctPoints(xValue, yValue, xBase, yBase, p) #(`xBase', `yBase') is added to (`xValue', `yValue').
            if p != 0:
                xValue = xValue % p #`xValue' is reduced modulo `p'.
                yValue = yValue % p #`yValue' is reduced modulo `p'.
            k -= 1 #k is reduced by one, since `xValue' and `yValue' have been increased by `xP' and `yP' respectively.
        else: #If the current value of k is even then `xBase' and `yBase' are increased instead.
            xBase, yBase = addIdenticalPoints(a, xBase, yBase, p) #(`xBase#, `yBase#) is added to itself.
            if p != 0:
                xBase = xBase % p #`xBase' is reduced modulo `p'. 
                yBase = yBase % p #`yBase' is reduced modulo `p'.
            k //= 2 #k is halved, because (`xBase', `yBase') has been doubled ((`xBase', `yBase') + (`xBase', `yBase') = 2(`xBase', `yBase')).
    return xValue, yValue #When the while loop ends, the algorithm will have set (`xValue', `yValue') = k(`xP', `yP') = kP.



def JacobiSymbol(y,x): #This function computes the Jacobi symbol (`y'/`x'), using the algorithm explained in the RSA section of this project.
    t = 1 #`t' is initialised to be equal to 1 and (unless `y' is congruent to 0 mod `x') will eventually be returned as the value of (`y'/`x').
    while y != 0:
        while y % 2 == 0: #Using properties (ii*) and (iii*) of the Jacobi symbol from the RSA section of this project, the powers of 2 in the prime factorisation of `y' can be removed and their Jacobi symbol computed, leaving `y' odd.
            y /= 2
            if x % 8 == 3 or x % 8 == 5:
                t *= -1
        if y < x: #If `y' is less than `x', then the Jacobi symbol can be flipped using property (iv*).
            c = y
            y = x
            x = c
            if y % 4 == 3 and x % 4 == 3: #The way in which (`y'/`x') relates to (`x'/`y') can be computed using property (iv*).
                t *= -1
        if y > x: #If `y' is greater than `x' then it can be reduced modulo `x'.
            y %= x #Using property (i*), (`y'/`x') = ((`y' mod `x')/`x').
        if y == 0:
            if x == 1:
                return(t) #If `x' = 1, then (`y'/`x') = `t'.
            if x != 1:
                return(0) #If `x' != 1, then we must have that `y' is a factor (or multiple) of `x', so (`y'/`x') = 0 by definition of the Jacobi symbol.



def generatePointOnCurve(p, a, b): #This function generates a random element from Ep(a,b).
    pointIsOnCurve = False
    while pointIsOnCurve == False: #The while loop runs until the a point P = (`xP', `yP') is generated that satisfies the condition that `yP'^{2} is congruent to (`xP'^{3} + `a'*`xP' + `b') mod (`p').
        pointIsSquare = False
        while pointIsSquare == False: #The while loop runs until `xP' satisfies the condition that `xP'^{3} + `a'*`xP' + `b' is a square number modulo `p'.
            xP = random.randint(0, p - 1) #A random value from Zp is chosen for `xP'.
            d = ((xP ** 3) + (a * xP) + b) % p #`d' = (`xP'^{3} + `a'*`xP' + `b') mod (`p') is computed.
            if JacobiSymbol(d, p) == 1:
                pointIsSquare = True #Note here that since `p' is prime, we are in fact computing the Legendre symbol, as defined earlier in the project, but we are using the algorithm for the Jacobi symbol since it runs identically. If the function returns 1, then by the definition of the Legendre symbol seen earlier, `d' is a square number modulo `p'.
        yP = modularExponentiation(d, (p + 1) // 4, p) #If `d' is a square number modulo `p', then since `p' was chosen to be congruent to 3 mod 4 we have that `d'^((`p' + 1)/4) mod `p' is (one of) the square roots of `d' mod `p'.
        if ((xP ** 3) + a*xP + b) % p == (yP ** 2) % p: #The fact that the point P = (`xP', `yP') satisfies the condition that y^{2} is congruent to x^{3} + ax + b mod p is checked here.
            return xP, yP



def babyStepGiantStep(a, b, p): #This function computes the baby-step giant-step algorithm for calculating the number of points on an elliptic curve over a finite field. The correctness of the algorithm is shown in the elliptic curve Diffie--Hellman key exchange section of this project.
    pointHasLargeOrder = False
    while pointHasLargeOrder == False: #The while loop runs until the randomly generated point (`xP', `yP') in Ep(a,b) has order larger than 4*`p'^{1/2}.
        xP, yP = generatePointOnCurve(p, a, b) #(`xP', `yP') is generated to be a random point in Ep(a,b).
        m = 4 * math.ceil(p ** (1/2))
        k = math.floor(2 * (p ** (1/4)))
        pointsOnCurve = [[xP, yP]] #This list will be iterated to contain the first 4ceil(`p'^{1/2}) points on the curve obtained by computing (`xP', `yP'), 2(`xP', `yP'), 3(`xP', `yP'), ..., 4ceil(`p'^{1/2})(`xP', `yP').
        babySteps = [] #This list will be set to contain the first floor(2`q'^{1/4}) elements in the list pointsOnCurve i.e. it will contain the elements (`xP', `yP'), 2(`xP', `yP'), 3(`xP', `yP'), ..., floor(2`q'^{1/4})(`xP', `yP').
        for n in range(2, m + 1): #This for loop iteratively computes the first 4ceil(`p'^{1/2}) points on the curve, as described above.
            if n == 2:
                xnP, ynP = addIdenticalPoints(a, xP, yP, p) #The first point added to pointsOnCurve is 2(`xP', `yP') = (`xP', `yP') + (`xP', `yP'), which must be computed using the formula for adding identical points.
            else:
                xnP, ynP = addDistinctPoints(xP, yP, xnP, ynP, p) #For `n'>2, `n'(`xP', `yP') is computed by adding (`xP', `yP') and (`n' - 1)(`xP', `yP').
            if [xnP, ynP] in pointsOnCurve: #If the point `n'(`xP', `yP') is already in pointsOnCurve, then the order of the point must not be large enough, so a new point will be generated.
                break
            else: #If the point is not in pointsOnCurve, then it is added to the list.
                pointsOnCurve.append([xnP, ynP])
                if n == k: #If `n' = `k' = floor(2`p'^{1/4}), then the list babySteps is set to be equal to the current value of the list pointsOnCurve (to be used later).
                    babySteps = pointsOnCurve
            if n == m: #If the for loop has reached this point then the order of the element (`xP', `yP') is sufficiently large, so the while loop ends.
                pointHasLargeOrder = True
    xQ, yQ = multiplyPoint(p + 1 + math.floor(2 * math.sqrt(p)), a, xP, yP, p) #The point (`xQ', `yQ') = (`q' + 1 + floor(2`q'^{1/2}))(`xP', `yP') is computed.
    giantSteps = [] #This list will be set to contain the elements (`xQ', `yQ') - `i'*`k'*(`xP', `yP') for `i' in range 1, 2, ..., `k'. 
    for i in range(1, k + 1):
        xanP, yanP = multiplyPoint(a * i, a, xP, yP, p) #First the point `i'*`k'*(`xP', `yP') is calculated.
        yanP *= -1 #Then the point -`i'*`k'*(`xP', `yP') = `i'*`k'*(`xP', -`yP') is calculated.
        if xQ == xanP and yQ == yanP:
            xqMinusanP, yqMinusanP = addIdenticalPoints(a, xQ, yQ, p) #The method for adding identical points is used if (`xQ', `yQ') = -`i'*`k'*(`xP', `yP').
        else:
            xqMinusanP, yqMinusanP = addDistinctPoints(xQ, yQ, xanP, yanP, p) #The method for adding distinct points is used if (`xQ', `yQ') != -`i'*`k'(`xP', `yP').
        giantSteps.append([xqMinusanP, yqMinusanP]) #(`xQ', `yQ') - `i'*`k'*(`xP', `yP') is added the the list giantSteps for the current value of `i'.
    t = 0
    for R in babySteps:
        if R in giantSteps: #Each element in the list babySteps is compared to each element in giantSteps to see if there is a match. 
            t = ((giantSteps.index(R) + 1) * k) + babySteps.index(R) + 1 #If babySteps[`i'] = giantSteps[`j'], then `t' is set to be equal to ((`i' + 1) * `k') + (`j' + 1).
    return xP, yP, p + 1 - t #The point (`xP', `yP'), along with the order of the curve, #Ep(a,b) = `p' + `1' - `t', are returned.
    


def generateEllipticCurveParameters(p): #This function generates the elliptic curve parameters `a' and `b'.
    curveIsSingular = True
    while curveIsSingular == True: #The while loop runs until the values of `a' and `b' satisfy the condition that 4`a'^{3} + 27`b'^{2} is not congruent to 0 mod `p'.
        a = random.randint(0, p - 1) #`a' is randomly generated to be in Zp.
        b = random.randint(0, p - 1) #`b' is randomly generated to be in Zp.
        singularityCondition = ((4 * modularExponentiation(a, 3, p)) + (27 * modularExponentiation(b, 2, p))) #This is the expression 4`a'^{3} + 27`b'^{2}.
        if singularityCondition % p != 0: #If `a' and `b' are such that the condition for non-singularity is satisfied, then the values of `a' and `b' are chosen for the curve parameters. Otherwise, new values are generated and tested.
            curveIsSingular = False
    return a, b



def primalityTestMillerRabin(p, repetitionsOfMillerRabin): #This function performs `repetitionsOfMillerRabin' repetitions of the Miller-Rabin primality test on the number `p'. 
    pMinusOneFactor = p - 1 #`pMinusOneFactor' is initialised to be `p' - 1. Since `p' is odd, `p' - 1 is even, and so `p' - 1 = (2^(k))*t for some natural numbers k and t, where t is odd.
    powerOfTwo = 0 #`powerOfTwo' is initialised to be 0, and is incremented to be equal to k (as defined above).
    while pMinusOneFactor % 2 == 0: #This while loop divides `pMinusOneFactor' by 2 until the resulting value is odd, incrementing `powerOfTwo' by 1 with each division. That is, it divides `pMinusOneFactor' by 2 and increments `powerOfTwo' k times until `pMinusOneFactor' = t and `powerOfTwo' = k, as k and t are defined above.
        pMinusOneFactor //= 2
        powerOfTwo += 1
    t = pMinusOneFactor #Since `pMinusOneFactor' = t (as t is defined above), the variable `t' is initialised for convenience.
    k = powerOfTwo #Since `powerOfTwo' = k (as k is defined above), the variable `k' is initialised for convenience.
    parametersTested = [] #This list keeps track of all the parameters used to test `p' for primality.
    for i in range(0, repetitionsOfMillerRabin): #This for loop repeats the Miller-Rabin primality test on `p' a number of times equal to `repetitionsOfMillerRabin'. Note that `for i in range(0, repetitionsOfMillerRabin)' here means for all i in {0, 1, 2, ..., `repetitionsOfMillerRabin' - 1} and so the loop runs `repetitionsOfMillerRabin' times.
        parameterTestedAlready = True
        while parameterTestedAlready == True: #This while loop generates parameters until a new one that hasn't been tested before is generated, at which point the loop breaks and the test begins.
            a = random.randint(2, p - 2) #Generates a random parameter to test the prime `p'.
            if a not in parametersTested:
                parametersTested.append(a)
                break
        at = modularExponentiation(a, t, p) #Initialises the variable `at' as `at' = `a'^(`t') mod (`p').
        if at != 1: #These nested if statements track the conditions of the Miller-Rabin primality test. If `a'^(`t') is not congruent to 1 or -1 mod (`p') and if `a'^(`t'*2^(`j')) is not congruent to -1 mod (`p') for all 1 <= `j' <= `k' - 1, then `p' is composite, in which case the function returns false. Otherwise, the code skips to the next loop where a new parameter `a' is generated and tested.
            if at != p - 1:
                for j in range(0, k):
                    at = modularExponentiation(at, 2, p)
                    if at != p - 1:
                        if j == k - 1: #If `p' has met the conditions of each if statement up to `j' = `k' - 1, then it has met all the requirements of the test to prove that `p' is composite.
                            return False #The fact that `p' is not prime is returned.
                        else:
                            continue
                    else:
                        break
                continue
            else:
                continue
        else:
            continue
    return True #If `p' has failed to be proven composite for each iteration of the for loop, then the probability that `p' is not prime is at most (1/4)^(-`repetitionsOfMillerRabin'), and so the fact that `p' is (almost certainly) prime is returned.



def generateLargeSpecificOddNumber(lowerBound, upperBound): #This function takes an upper and lower bound for a potential prime, and generates numbers in that range until an odd one is found. This eliminates trivially non-prime numbers and theoretically halves the number of numbers that would need to be tested before a prime is found (as mentioned previously in the RSA section of this project).
    pIsSpecificOdd = False #The boolean variable `pIsOdd' (determining whether or not `p' is an odd number congruent to 3 mod 4) is initialised to be false.
    while pIsSpecificOdd == False: #This while loop runs until a generated `p' is odd and congruent to 3 mod 4.
        p = random.randint(lowerBound, upperBound) #`p' is defined to be a random integer between `lowerBound' and `upperBound' (inclusive).
        if p % 4 == 3: #If `p' is congruent to 3 mod 4 then it is also trivally odd, so the loop ends. Otherwise another value of `p' is generated.
            pIsSpecificOdd = True
    return p #The generated odd number `p' congruent to 3 mod 4 is returned to be tested for primality.



def modularExponentiation(base, exponent, modulus): #This function performs modular exponentiation using a square-and-multiply algorithm, reducing intermediate steps modulo `modulus'. The algorithm can also perform exponentiation without reducing intermediate steps, if desired, by passing 0 as the `modulus' parameter (since performing calculations modulo 0 isn't defined anyway).
    value = 1 #The variable `value' is initialised to 1, and is returned as `value' = `base'^(`exponent') mod (`modulus').
    while exponent > 0: #The square-and-multiply algorithm based on the one described in the RSA section of this project runs by incrementally increasing `value' based on the current value of `exponent`, until `exponent' = 0.
        if exponent % 2 == 1: #If `exponent' is odd, then `value' is multiplied by `base' and `exponent' is decremented by 1.
            value = value * base
            if modulus != 0: #If the value of `modulus' is non-zero, then `value' is reduced modulo `modulus' between calculations.
                value = value % modulus
            exponent = exponent - 1
        else: #If `exponent' is even, then `base' is squared and `exponent' is halved.
            base = base * base
            if modulus != 0: #If the value of `modulus' is non-zero, then `base' is reduced modulo `modulus' between calculations.
                base = base % modulus
            exponent //= 2
    return value #The variable `value' (which now equals `base'^(`exponent') mod (`modulus')) is passed back to wherever modularExponentiation() was called from.



def generateLargePrime(bitLength, repetitionsOfMillerRabin): #This function generates a prime number `p' of the desired size such that `p' is congruent to 3 mod 4.
    lowerBound = modularExponentiation(2, bitLength - 1, 0) #The lower bound for `p' is set to be the smallest `bitLength' bit number.
    upperBound = modularExponentiation(2, bitLength, 0) - 1 #The upper bound for `p' is set to be the largest `bitLength' bit number.
    pIsProbablyPrime = False
    while pIsProbablyPrime == False: #The while loop runs while `p' is not a prime number congruent to 3 mod 4
        p = generateLargeSpecificOddNumber(lowerBound, upperBound) #Generates an odd number `p' congruent to 3 mod 4
        pIsProbablyPrime = primalityTestMillerRabin(p, repetitionsOfMillerRabin) #Tests `p' for primality using `repetitionsOfMillerRabin' repetitions of the Miller-Rabin test.
    return p



def generateEllipticCurve(bitLength, repetitionsOfMillerRabin): #This function generates a group of points on an elliptic curve over a finitie field Ep(a,b) with prime order and chooses a point at random in the group as a generator.
    groupOrderIsPrime = False
    while groupOrderIsPrime == False: #Runs until the group generated has a prime number of elements.
        p = generateLargePrime(bitLength, repetitionsOfMillerRabin) #`p' is generated to be a prime of the required bit length and is tested with the given number of repetitions of the Miller-Rabin primality test.
        a, b = generateEllipticCurveParameters(p) #The curve parameters `a' and `b' are generated so that the curve with equation y^{2} = x^{3} + `a'x + `b' is not singular.
        xG, yG, groupOrder = babyStepGiantStep(a, b, p) #The size of Ep(a,b) is determined using the baby-step giant-step algorithm and a point G = (`xG',`yG') on the curve is chosen as the generator of the group.
        groupOrderIsPrime = primalityTestMillerRabin(groupOrder, repetitionsOfMillerRabin) #The order of Ep(a,b) is tested for primality using the Miller-Rabin test.
    return p, a, b, xG, yG



def main():
    bitLength = 9 #The bit length of the prime `p' used to generated the group of points on the elliptic curve.
    repetitionsOfMillerRabin = 100 #The number of times `p' is tested for primality.
    p, a, b, xG, yG = generateEllipticCurve(bitLength, repetitionsOfMillerRabin) #The curve parameters `p', `a', and `b' are generated. as well as a point G = (`xG', `yG') on the curve to act as a generator of the group of points Ep(a,b).
    Ni, xMi, yMi = generateKeys(p, a, xG, yG) #The public and private keys for some user I are generated.
    Nj, xMj, yMj = generateKeys(p, a, xG, yG) #The public and private keys for some user J are generated.
    xNiMj, yNiMj = multiplyPoint(Ni, a, xMj, yMj, p) #This is user I's method of generating their shared secret with user J.
    xNjMi, yNjMi = multiplyPoint(Nj, a, xMi, yMi, p) #This is user J's method of generating their shared secret with user I.



main() #This just calls the main() function.