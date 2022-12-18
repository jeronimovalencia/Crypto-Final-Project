###   Global Variables (used in Shanks-Tonelli algorithm)   ###
go = 0
x = 0
B = 0
g = 0
r = 0
exp = 0
e = 0
s = 0
n = 0
found = 0

###   1) Compute the number of rational points E(Fp) using Legendre Symbols   ###

function legendre_symbol_formula(x,p)
    num = mod(big(x)^(Integer((p-1)/2)),p)
    if num == 0
        0
    elseif num == 1
        1
    elseif num == mod(-1,p)
        -1
    end
end

function brute_force(a,b,p)
    Fp = (0:p-1)
    squares = [mod(i^2,p) for i in Fp]
    E = zeros(0)
    ans = 0
    for i in Fp
        val = mod(i^3+a*i+b,p)        
        #ans = ans + legendre_symbol_squares(val,p,squares)
        ans = ans + legendre_symbol_formula(val,p)
    end
    return ans+1+p
end

###   2) Use baby-step giant-step with group structure of E(Fp)   ###

#Square roots in Fp (Shanks-Tonelli algorithm)

function square_root_mod_p(a,p)
    res = big(a)^Integer((p-1)/2)
    res = mod(res,p)
    # If the number a is not a square mod p:
    if mod(res-p+1,p) == 0
        return "NotSquare"
    elseif mod(res-1,p) == 0
        # Find e and s such that p-1 = s * 2^e
      
        global exp = 1
        global N = p-1
        global go = 1 
        global e = 0
        global s = 0

        while go == 1
            if isinteger(N/(big(2)^exp))
                global exp = exp+1
            else
                global e = exp-1
                global s = Integer(N/(big(2)^(exp-1)))
                global go = 0
            end
        end
        
        # Find a number n that is not a square mod p
        
        global go = 1 
        global n = 2
        while go == 1
            if mod(big(n)^Integer((p-1)/2),p) == 1
                global n = n+1
            else
                global go = 0
            end
        end
        
        # Initialize variables for the algorithm
        
        #First guess for the square root
        global x = mod(big(a)^(Integer((s+1)/2)),p)
        
        #First guesss for the fudge factor
        global B = mod(big(a)^s,p)
        
        global g = mod(big(n)^s,p)
        global r = mod(e,p)
        global found = 0        
        
        #Look for the square root:
        
        while found == 0
            # Find m such that 0 <= m <= r-1 and b^(2^m) = 1 mod p
            global m = 0
            global go = 1
            global num = B
            
            if B == 1
                    go = 0
                    m = 0
            end
            while go==1
                global num = mod(big(num)^2,p)
                if mod(num,p) == 1
                    global go = 0
                    global m = m+1
                else
                   global m = m+1 
                end
            end

            # Evaluate if we found the root

            if m==0
                global found = 1
                return x
                
            elseif m>0
                global x = mod(x*big(g)^(2^(r-m-1)),p)
                global B = mod(B*big(g)^(2^(r-m)),p)
                global g = mod(big(g)^(2^(r-m)),p)
                global r = mod(m,p)
                
            else
                global found = 1
                println("Something is wrong!")
            end
        end
    else
        println("Something bad happened")
    end    
end

#Elliptic curve group structure:

function inverse_mod_p(x,p)
    return gcdx(x,p)[2]
end

function point_in_curve(x,a,b,p)
    return [mod(x,p), mod(square_root_mod_p(mod(x^3+a*x+b,p),p),p),0]
end

function inverse(P,a,b,p)
    return [P[1],mod((-1)*P[2],p),P[3]]
end


function addition(P,Q,a,b,p)
    # If either P or Q are the identity [0,0,1]
    if P[3] == 1
        return Q
    elseif Q[3] == 1
        return P
    end
    
    # If neither P or Q are the identity
    
    #If they are equal
    if mod(P[1]-Q[1],p) == 0 && mod(P[2]-Q[2],p) == 0
        slope = mod(3*P[1]^2+a,p)*mod(inverse_mod_p(2*P[2],p),p)
        return [mod(slope^2-2*P[1],p),
                mod(slope*(P[1]-(slope^2-2*P[1]))-P[2],p),0]
    
    #If they are inverses
    elseif mod(P[1]-Q[1],p) == 0 && mod(P[2]+Q[2],p) == 0
        return [0,0,1]
    
    #If they are different points
    else
        slope = mod(P[2]-Q[2],p)*mod(inverse_mod_p(P[1]-Q[1],p),p)
        return [mod(slope^2-P[1]-Q[1],p),
                mod(slope*(P[1]-(slope^2-P[1]-Q[1]))-P[2],p),0]
    end
end
    
function n_times_point(n,P,a,b,p)
    last = P
    for i in (1:n-1)
        last1 = addition(P,last,a,b,p)
        last = last1
    end
    return(last)
end

#Point counting of E(Fp) using baby-step giant-step:

function baby_step_giant_step(a,b,p)
    Fp = (0:p-1)
    
    #Pick a random P in E(Fp)
    
    done = 0
    P = zeros(0)
    
    while done == 0
        x = rand(Fp)
        if(mod(big(mod(x^3+a*x+b,p))^((p-1)/2),p) == 1)
            done = 1
            P = point_in_curve(x,a,b,p) 
        end
    end
    
    # Baby steps
    
    BSlist = [[0,0,1],P,inverse(P,a,b,p)]
    s = Integer(floor(float(p)^(1/4)))
    
    for i in (1:s-1)
        last = BSlist[length(BSlist)-1]  
        newP = addition(last,P,a,b,p)
        BSlist = push!(BSlist,newP)
        BSlist = push!(BSlist,inverse(newP,a,b,p))
    end
    
    # Giant Steps
    L = length(BSlist)
    Q1 = addition(BSlist[L],BSlist[L],a,b,p)
    Q = addition(P,Q1,a,b,p)
    R = n_times_point(p+1,P,a,b,p)
    t = Integer(floor(2*sqrt(p) / (2*s+1)))    
    
    GSlist = [R,addition(R,Q,a,b,p),addition(R,inverse(Q,a,b,p),a,b,p)]
    
    for i in (1:t-1)
        newR1 = addition(Q,GSlist[length(GSlist)-1],a,b,p)
        newR2 = addition(inverse(Q,a,b,p),GSlist[length(GSlist)],a,b,p)
        GSlist = push!(GSlist,newR1)
        GSlist = push!(GSlist,newR2)        
    end
    
    #Search for i and j such that R+iQ = jP
    
    ret = 0
    for i in (1:length(GSlist))
        gs = GSlist[i]
        for j in (1:length(BSlist))
            bs = BSlist[j]
            if mod(gs[1]-bs[1],p) == 0 && mod(gs[2]-bs[2],p) == 0 && mod(gs[3]-bs[3],p) == 0 
                ni = 0
                nj = 0
                if i>0 && i%2 == 0
                    ni = Integer(i/2)
                elseif i>0 && i%2 == 1
                    ni = (-1)*(Integer(floor(i/2)))
                end
                if j>0 && j%2 == 0
                    nj = Integer(floor(j/2))
                elseif j>0 && j%2 == 1
                    nj = (-1)*(Integer(floor(j/2)))
                end
                ret = 1                
                return p+1+(2*s+1)*ni-nj
            end
        end
    end
    if(ret == 0)
        return "Something bad happened."
    end
end

###   3) Generalization for #E(Fq) with q=p^m with p prime and m>1   ###

function inverse_mod_q(x,p,m)
    return gcdx(x,p^m)[2]
end

#Elliptic curve E(Fq)

function point_in_curve_generalized(x,a,b,p,m)
    q = p^m
    r = p^(m-1)
    y_squared = x^3+a*x+b
    root = mod(square_root_mod_p(y_squared,p),p)
    expo = Integer((q-2*r+1)/2)
    y = mod((big(root)^r)*mod(big(y_squared),q)^expo,q)
    return [mod(x,q), mod(y,q),0]
end

function inverse_q(P,a,b,p,m)
    return [P[1],mod((-1)*P[2],p^m),P[3]]
end

function addition_q(P,Q,a,b,p,m)
    q = p^m
    
    # If either P or Q are the identity [0,0,1]
    if P[3] == 1
        return Q
    elseif Q[3] == 1
        return P
    end
    
    # If neither P or Q are the identity
    
    #If they are equal
    if mod(P[1]-Q[1],q) == 0 && mod(P[2]-Q[2],q) == 0
        slope = mod(3*P[1]^2+a,q)*mod(inverse_mod_q(2*P[2],p,m),q)
        return [mod(slope^2-2*P[1],q),
                mod(slope*(P[1]-(slope^2-2*P[1]))-P[2],q),0]
    
    #If they are inverses
    elseif mod(P[1]-Q[1],q) == 0 && mod(P[2]+Q[2],q) == 0
        return [0,0,1]
    
    #If they are different points
    else
        slope = mod(P[2]-Q[2],q)*mod(inverse_mod_q(P[1]-Q[1],p,m),q)
        return [mod(slope^2-P[1]-Q[1],q),
                mod(slope*(P[1]-(slope^2-P[1]-Q[1]))-P[2],q),0]
    end
    
end
    
function n_times_point_q(n,P,a,b,p,m)
    last = P
    for i in (1:n-1)
        last1 = addition_q(P,last,a,b,p,m)
        last = last1
    end
    return(last)
end

#Algorithm to find #E(Fq)

function baby_step_giant_step_generalized(a,b,p,m)
    q = p^m
    Fq = (0:q-1)
    ret = 0
    while ret == 0
        #Pick a random P in E(Fq)

        done = 0
        P = zeros(0)

        while done == 0
            x = rand(Fq)
            if(mod(big(mod(x^3+a*x+b,p))^((p-1)/2),p) == 1)
                done = 1
                P = point_in_curve_generalized(x,a,b,p,m) 
            end
        end

        # Baby steps

        BSlist = [[0,0,1],P,inverse_q(P,a,b,p,m)]
        s = Integer(floor(float(q)^(1/4)))

        for i in (1:s-1)
            last = BSlist[length(BSlist)-1]  
            newP = addition_q(last,P,a,b,p,m)
            BSlist = push!(BSlist,newP)
            BSlist = push!(BSlist,inverse_q(newP,a,b,p,m))
        end

        # Giant Steps

        L = length(BSlist)
        Q1 = addition_q(BSlist[L],BSlist[L],a,b,p,m)
        Q = addition_q(P,Q1,a,b,p,m)
        R = n_times_point_q(p+1,P,a,b,p,m)
        t = Integer(floor(2*sqrt(q) / (2*s+1)))    

        GSlist = [R,addition_q(R,Q,a,b,p,m),
                            addition_q(R,inverse_q(Q,a,b,p,m),a,b,p,m)]

        for i in (1:t-1)
            newR1 = addition_q(Q,GSlist[length(GSlist)-1],a,b,p,m)
            newR2 = addition_q(inverse_q(Q,a,b,p,m),
                                GSlist[length(GSlist)],a,b,p,m)
            GSlist = push!(GSlist,newR1)
            GSlist = push!(GSlist,newR2)        
        end

        #Search for i and j such that R+iQ = jP

        for i in (1:length(GSlist))
            gs = GSlist[i]
            for j in (1:length(BSlist))
                bs = BSlist[j]
                if (mod(gs[1]-bs[1],q) == 0 && 
                    mod(gs[2]-bs[2],q) == 0 && 
                    mod(gs[3]-bs[3],q) == 0)

                    ni = 0
                    nj = 0
                    if i>0 && i%2 == 0
                        ni = Integer(i/2)
                    elseif i>0 && i%2 == 1
                        ni = (-1)*(Integer(floor(i/2)))
                    end

                    if j>0 && j%2 == 0
                        nj = Integer(floor(j/2))
                    elseif j>0 && j%2 == 1
                        nj = (-1)*(Integer(floor(j/2)))
                    end
                    ret = 1                
                    return q+1+(2*s+1)*ni-nj
                end
            end
        end
    end
end;