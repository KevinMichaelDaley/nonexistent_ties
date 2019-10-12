import numpy as np
import networkx as nx
import scipy
from sympy import *
import sys, json
from copy import copy,deepcopy

def gcg(A,aa,augment=True, alpha=1.0, debug_print=False):
    """gcg (for Generalized Connection Graph) is a routine which accepts:
        an adjacency matrix A,
        an intrinsict stability parameter a (see associated paper for details),
        a boolean parameter 'augment' (True to use the new method or False -> the old method)
        a real parameter alpha which controls the optimization subroutine (see the description of the algorithm in the associated paper; alpha=0 corresponds to no optimization performed)
        a boolean parameter debug_print which does exactly what it sounds like, prints debug information about the reroutings performed by the optimization (probably you want it set to False).
    """

    N=A.shape[0] #N is the number of nodes (dimension of the adjacency matrix)
    unbalance=np.sum(A,1)-np.sum(A,0) #compute the degree imbalance of every node by subtracting the out-degree from the in-degree using numpy's shorthand
    mean_unbalance=np.zeros([N,N]) #initialize the mean degree imbalance to 0 and, 
    for i in range(N):
        for j in range(N): #for every directed node pair ij,
            if i!=j:
                mean_unbalance[i,j]=(unbalance[i]+unbalance[j]) #compute the mean imbalance if i!=j
            else:
                A[i,j]=0 #otherwise, remove the self-edge because they cannot affect synchrony (the difference variable is identically 0)
    #we could also compute this as mean_unbalance=np.add.outer(unbalance,unbalance)/2.0
    augmented=np.abs(np.minimum(mean_unbalance,0))/(2.0*N)*((A+A.T>0) if not augment else 1) #for every node pair (augmented version) or every symmetrized edge (old version), if mean_unbalance[i,j]<0 then add the appropriate coupling strength (unbalance[i]+unbalance[j]/2N).  
    Aaug=(A+A.transpose())/2.0+augmented #symmetrize the graph and add the extra coupling strength, store in Aaug
    G=nx.from_numpy_matrix(Aaug>0) #create a networkx graph from Aaug so we can apply their dijkstra implementation to compute (a set of) the shortest paths between each node
    r=np.zeros((N,N)) #we define two arrays r and l s.t. for each edge k, b_k =l_k + r_k*d
    l=np.zeros((N,N)) #therefore, l_k is the unweighted version of b_k corresponding to the undirected method
                      #r_k contains all the extra weighting terms (by mean degree imbalance)
                      #this makes it possible to rearrange the main inequality on each edge and obtain a numerical bound for d
                      #the bound (for edge e_ij) is d[i,j]=a/N*l[i,j]/(Aaug[i,j]-a/N*r[i,j]) by simple algebraic substition and rearrangement

    q=[] #this is our queue of configurations which the optimization wants to try
    visited=[] #this is the list of reroutings which the optimization has already tried and therefore won't visit again
    paths0=dict(nx.all_pairs_shortest_path(G)) #this is the original set of shortest paths between node pairs; we have to convert it to a dict from a generator
    eps_hist=[] #this tells us if we have hit a minimum bound which is not a local minimum
    q.append(paths0) #and then seed the queue with it as the first configuration
    it=0 #the iteration count for the optimization; if alpha==0 terminate before incrementing this value
    eps_min=1e9 #the current best bound.  set it to something really high so any good bound on the first iteration will improve on it.
    while len(q)>0: #while we still have configurations in the queue to consider
        summand=1#diagnostic variable which stores and returns the denominator of the bound, since sometimes it can be negative, corresponding to
        #an unsolvable inequality and therefore an inconsistency in the algorithm, in which case we want to know how bad it was and where it happened
        r=np.zeros((N,N))#reinitialize r and l
        l=np.zeros((N,N))
        if debug_print:#diagnostic output regarding the optimization progress
            sys.stderr.write("%i work items\n"%len(q))
            sys.stderr.write("%f best solution\n"%eps_min)
            sys.stderr.flush()
        paths=q[0] #retrieve a configuration from the head of the queue
        q=q[1:] #and pop it off the queue
        for i in range(N-1): #for every undirected, nonzero-length path between two nodes i and j
            for j in range(i+1,N): 
                if i==j:
                    continue
                P=list(paths[i][j])  #set P equal to the path between i and j
                if augmented[i,j]!=0 and A[i,j]==0 and A[j,i]==0 and P[0]==i and P[1]==j: #if P is just an augmented edge between i and j directly
                    l[i,j]+=1 #L(P)=1
                    l[j,i]+=1
                else: #otherwise, add the weighted path length terms to l and r for every edge along the path
                    for k in range(len(P)-1): 
                        u=P[k]
                        v=P[k+1]
                        l[u,v]+=len(P)-1 #the length of the path is added to l unweighted as discussed
                        l[v,u]+=len(P)-1
                        r[u,v]+=(len(P)-1)*max((unbalance[j]+unbalance[i])/(2.0*aa),0) #to r is added any weighting due to the mean node degree imbalance (which has no effect if negative)
                        r[v,u]+=(len(P)-1)*max((unbalance[j]+unbalance[i])/(2.0*aa),0)
        eps=0 #the current worst bound (over all the edges, reset every iteration)
        eps_argmax=[0,0] #the bottleneck edge, which must be rerouted
        reroute_edge=np.zeros([N,N]) #matrix of 1s for all the edges we want to reroute, 0s otherwise
        early_out=False #we don't want to reroute a configuration that didn't produce a bound
        for i in range(N-1):#for each undirected node pair in the graph,
                for j in range(i+1,N):
                    if Aaug[i,j]>0:#for which an edge exists in the symmetrized and augmented graph,
                            num=aa*l[i,j]/N
                            denom=Aaug[i,j]-aa*r[i,j]/N #as discussed, algebraic rearrangement of the main inequality so that d=num/denom
                                                        #note that denom, and thus d, is not guaranteed to be positive.
                            summand=min(summand,denom)
                            if num/denom<0 or denom<0:#if d<0 then we cannot solve the inequality
                                early_out=True
                                eps=1e9
                                reroute_edge[i,j]=1
                                reroute_edge[j,i]=1
                                if debug_print:
                                    sys.stderr.write("inconsistency found at %i,%i: %f %f\n"%(i,j, Aaug[i,j],r[i,j]))
                                    sys.stderr.flush()
                            if denom==0: #if the denominator==0 then the solution is infinite
                                eps=1e9
                                early_out=True
                                reroute_edge[i,j]=1
                                reroute_edge[j,i]=1
                                if debug_print:
                                    sys.stderr.write("inconsistency found at %i,%i: %f %f\n"%(i,j,Aaug[i,j],r[i,j]))
                                    sys.stderr.flush()
                            else: #otherwise, determine if this is the new bottleneck edge
                                if eps<(num/denom):#if it is, update eps, the maximum bound, to the bound on this edge
                                    eps=(num/denom)
                                    if debug_print:
                                        sys.stderr.write("(%i, %i): (%f %f %f %f %f)\n"%(i,j,l[i,j],r[i,j],num,denom,num/denom))
                                    eps_argmax=[i,j] #and assign it as the bottleneck edge
        reroute_edge[eps_argmax[0],eps_argmax[1]]=1 #we need to reroute the bottleneck edge
        reroute_edge[eps_argmax[1],eps_argmax[0]]=1 #in both directions!
        if eps<eps_min and not early_out: #if our new bound is better than the current best bound (over all iterations) and we didn't encounter an inconsistent inequality
                eps_min=eps #update that to the new bound
        if early_out: #if we can't solve the inequality
            sys.stderr.write("inconsistencies found\n")
            if alpha==0.0: #don't consider reroutings of this configuration because it's probably not going to improve anything
              break
            continue
        it+=1
        if alpha==0.0:
            break
        eps_hist.append(eps)
        if eps<=alpha*eps_min:#otherwise, but only if the new bound satisfies the optimality criterion (no worse than alpha* the 
            if np.all(np.array(eps_hist[-N:])<=eps_min) and len(eps_hist)>N:#and if we have not been stuck at the same bound for a very long time
                break
            for u in range(N):
                for v in range(N):#for every directed node pair u,v
                    if reroute_edge[u,v] and Aaug[u,v]: #if uv needs to be rerouted
                        e=[u,v]
                        for w in range(N): #consider every vertex w adjacent to u
                            if Aaug[u,w]==0:
                                continue
                            uvw_triple=sorted([u,v,w])  #if uv has been rerouted through w, or any other such combination
                            visited_index=uvw_triple[0]*N*N+uvw_triple[1]*N+uvw_triple[2] #then we don't want to try it again unless we are rerouting a different path.
                            paths2={}  #create a new list of shortest paths which is a copy of the current one
                            rerouted=False
                            for i2 in range(N-1):
                                paths2[i2]={}
                                for j2 in range(i2+1,N): #if there is a path i->j containing edge u->v as a subpath, reroute it as i->u -> w -> j
                                    paths2[i2][j2]=[]
                                    for ni,node in enumerate(paths[i2][j2]):
                                        paths2[i2][j2].append(node)
                                        if visited_index*N*N+i2*N in visited: #unless we've already visited that rerouting of that path
                                            pass
                                        elif min(u,v)!=i2 and max(u,v)!=j2 and w not in paths[i2][j2] and ni<len(paths[i2][j2])-1 and not rerouted:
                                            nextnode=paths[i2][j2][ni+1]
                                            if (node==u and nextnode==v):
                                                paths2[i2][j2]+=paths[w][j2] if w<j2 else reversed(paths[j2][w])
                                                visited.append(visited_index*N*N+i2*N)
                                                if debug_print:
                                                    sys.stderr.write('rerouting path %i %i (%i %i => %i %i %i)\n'%(i2,j2,u,v,u,w,v))
                                                rerouted=True
                                                break
                                                
                            if rerouted: #if we ended up finding such a rerouting which was unvisited
                                q.append(paths2) #then let's add the whole configuration to the queue and see if it is better
    num_aug=np.sum(augmented>0)/2 #count the number of augmented edges
    return eps_min, floor(num_aug), summand #return the best bound, the number of augmented edges, and the diagnostic output
find_gcg=gcg
def msf(A,a):#msf is a routine to compute a/Re(lambda_2) given adjacency matrix A and intrinsic stability parameter a
        N=A.shape[0]
        rsum=np.zeros(N)
        for i in range(N):
            rsum[i]=np.sum(A[:,i])
        w,v=np.linalg.eig(A-np.diag(rsum))
        wbar=sorted(np.abs((np.real(w))))
        return a/wbar[1]

if __name__=="__main__":#example usage, main routine if file is called as a program
        A=np.loadtxt(sys.argv[1])
        a=7.79 #corresponds to the chaotic Lorenz system with x-coupling
        N=A.shape[0]
        daug,naug,s0=find_gcg(A,a,True,0.0)
        daug1,naug,s1=find_gcg(A,a,True,1.0)
        daug0,z,s02=find_gcg(A,a,False,0)
        daug2,z,s2=find_gcg(A,a,False,1.0)
        Asym=(A+A.T)/2.0 #if we want we can compare this to the algebraic connectivity of the symmetrized graph
        print( naug, msf(A,a), daug, daug1,daug0, daug2, msf(Asym,a))

                
