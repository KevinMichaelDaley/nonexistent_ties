#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <assert.h>
#include <pthread.h>
#define FLT_MAX 3e38
#define MAX( x,y ) ( ( x > y ) ? x : y )
#define MIN( x,y ) ( ( x < y ) ? x : y )
typedef float Complex[2];
struct path_choice_queue {
    //stores all paths associated with a particular choice of paths between every node pair
    //paths are stored in reverse, from end to start.
    //this struct represents one node of a queue which is processed sequentially.
	int* all_pairs_paths;
	struct path_choice_queue* next;
};

void* alloc_seq( struct path_choice_queue* qseq, int nbatch, int N, int* qseq_head ) {//we use a fixed-sized circular array buffer queue to save on little dynamic allocations, which are expensive and lead to fragmentation and heap corruption.
	int diam = N;
	int qhead0 = qseq_head[0]++;
	qseq_head[0] %= nbatch;
	struct path_choice_queue* q = &( qseq[qhead0] );
	if ( q->all_pairs_paths == NULL ) {
		q->all_pairs_paths = malloc( N * N * diam * sizeof( int ) );
		memset( q->all_pairs_paths,255,N * N * diam * sizeof( int ) );
	}
	return q;
}


void build_path_from_predecessors( int* path, int i, int j, int* choice, int* pi, int N, float* dist, float* Aaug ) {
	int diam = N;
	if ( i == j ) {
		path[0] = i;

	} else if ( Aaug[i * N + j] != 0 )            {
		path[0] = j;
		path[1] = i;
	} else if ( dist[i * N + j] > N * N )              {
		return;
	} else {
		int n = 0;
		for ( n = 0; n <= choice[i * N + j]; ++n ) {
			if ( pi[( i * N + j ) * diam + choice[i * N + j]] >= 0 ) {
				break;
			}
		}
		build_path_from_predecessors( &( path[1] ),i,pi[( i * N + j ) * diam + choice[i * N + j] - n],choice,pi,N, dist, Aaug );
		path[0] = j;
	}
}
void build_queue_from_predecessor_matrix( struct path_choice_queue** q,
                                          int* pi, 
                                          int* permutation,
                                          float* dist,
                                          int N, 
                                          int nbatch, 
                                          void* qseq, 
                                          int* qseq_head, 
                                          float* Aaug ) {
     //given a precessesor matrix computed by floyd-warshall algorithm, 
    //initialize the queue of path choices for processing
	int i,j,k, diam = N;
	q[0] = alloc_seq( qseq, nbatch, N, qseq_head );
	q[0]->next = NULL;
	for ( i = 0; i < N; ++i ) {
		for ( j = 0; j < N; ++j ) {
			if ( i == j ) {
				continue;
			}
			if ( dist[i * N + j] >= N * N ) {
				continue;
			}
			if ( Aaug[i * N + j] != 0 ) {
				q[0]->all_pairs_paths[( i * N + j ) * diam + 0] = j;
				q[0]->all_pairs_paths[( i * N + j ) * diam + 1] = i;
				continue;
			}
			for ( k = 0; k < diam; ++k ) {
				q[0]->all_pairs_paths[diam * ( i * N + j ) + k] = -1;
			}
			build_path_from_predecessors( &( q[0]->all_pairs_paths[( i * N + j ) * diam] ), i,j, permutation, pi,N, dist, Aaug );
			permutation[i * N + j]++;
			if ( permutation[i * N + j] > diam - 1 ) {
				permutation[i * N + j]--;
				continue;
			}
			if ( pi[( i * N + j ) * diam + permutation[i * N + j]] < 0 ) {
				permutation[i * N + j]--;
				continue;
			}
			build_queue_from_predecessor_matrix( &( q[0]->next ),pi,permutation, dist, N, nbatch, qseq, qseq_head, Aaug );
			permutation[i * N + j]--;
		}
	}
}
float run_connection_graph_method_for_path_choice( struct path_choice_queue* q, 
                                                   int* reroute_edge,
												   float* mean_node_unbalance,
												   float twocell,
												   int N,
												   int directed, 
                                                   float* Aaug ) {
    //perform the computation of bound for a given choice of paths
	int diam = N;
	int i,j,k;
	if ( directed ) {
        //directed networks are treated separately due to node unbalance
		float* lhs = alloca( N * N * sizeof( float ) );
		float* rhs = alloca( N * N * sizeof( float ) );
		memset( lhs,0,N * N * sizeof( float ) );
		memset( rhs,0,N * N * sizeof( float ) );
		float eps = 0.0;
		float lhsavg = 0.0;
		for ( i = 0; i < N; ++i ) {
			for ( j = i + 1; j < N; ++j ) {
                //for each node pair
				if ( i == j ) {
					continue;
				}
				//compute the path length by linearly iterating over entries until we reach the start node
				//(recall that paths are stored backwards due to the order in which predecessors are computed and stored)
				int d;
				for ( d = 0; d < diam && q->all_pairs_paths[( i * N + j ) * diam + d] != i; ++d ) {}
				if ( d == diam ) {
					continue;
				}
				if ( d == 1 && mean_node_unbalance[i * N + j] < 0 ) {
					lhs[i * N + j] += 1;
					lhs[j * N + i] += 1;
					continue;
				}
				float W = MAX( mean_node_unbalance[i * N + j] / twocell + 1,0 );


				if ( W == 0 ) {
					continue;
				}
				for ( k = 0; k < d; ++k ) {
                    //store the terms of the inequality for each edge in the path
					int u = q->all_pairs_paths[( i * N + j ) * diam + k];
					int v = q->all_pairs_paths[( i * N + j ) * diam + k + 1];
					if ( u == v ) {
						continue;
					}
					int P = d;
					lhs[v * N + u] += P;
					rhs[v * N + u] += P * ( W - 1 );
					lhs[u * N + v] += P;
					rhs[u * N + v] += P * ( W - 1 );
				}
			}
		}
		int Nedges = 0;
		float lhsmax = 0;
        //for every node pair
		for ( i = 0; i < N; ++i ) {
			for ( j = 0; j < N; ++j ) {
				if ( Aaug[i * N + j] > 0 ) {
                    //if there is an edge, determine if it is a bottleneck edge for the purpose of rerouting
					lhsmax = MAX( lhs[i * N + j], lhsmax );
					++Nedges;
				}
			}
		}
		
        //for every node pair
		for ( i = 0; i < N; ++i ) {
			for ( j = 0; j < N; ++j ) {
				if ( i == j ) {
					continue;
				}
				int d;
                //compute the length of the path from i to j by iteration as before
				for ( d = 0; d < diam && q->all_pairs_paths[( i * N + j ) * diam + d] != i; ++d ) {}

				if ( d == diam ) {
					continue;
				}
				if ( d == 1 && mean_node_unbalance[i * N + j] < 0 ) {
					continue;
				}
                //for every edge along the path between i and j, if one exists and is not of length 1
				for ( k = 0; k < d; ++k ) {
					int u = q->all_pairs_paths[( i * N + j ) * diam + k];
					int v = q->all_pairs_paths[( i * N + j ) * diam + k + 1];
                    //reroute the edge if it is a bottleneck
					if ( lhs[v * N + u] >= lhsmax - 0.0000001 ) {
						reroute_edge[u * N + v] = 1;
					}
				}
			}
		}
        //for every node pair
		for ( i = 0; i < N; ++i ) {
			for ( j = i + 1; j < N; ++j ) {

				if ( Aaug[i * N + j] == 0 || fabs( Aaug[i * N + j] * N - twocell * rhs[i * N + j] ) < 0.001 ) {
					continue;
				}
				if ( lhs[i * N + j] == 0 ) {
					continue;
				}
				//solve the inequality and if we have a bottleneck edge for the purpose of computing the bound,
				//then store the result as the current maximum
				eps = MAX( eps,twocell * ( lhs[i * N + j] / ( N * Aaug[i * N + j] + twocell * rhs[i * N + j] ) ) );
			}
		}
		if ( eps == 0 ) {
			return FLT_MAX;
		}
		return eps;
	} else {//undirected, unweighted case
        //here we just compute maximal b_k and return it scaled
		int* b = alloca( N * N * sizeof( float ) );
		memset( b,0,N * N * sizeof( float ) );
		for ( i = 0; i < N; ++i ) {
			for ( j = 0; j < i; ++j ) {
				if ( i == j ) {
					continue;
				}

				int d;
				for ( d = 0; d < diam; ++d ) {
					if ( q->all_pairs_paths[( i * N + j ) * diam + d] == i ) {
						break;
					}
				}

				for ( k = 0; k < d; ++k ) {
					int u = q->all_pairs_paths[( i * N + j ) * diam + k];
					int v = q->all_pairs_paths[( i * N + j ) * diam + k + 1];
                    //FIXME: incorporate weights
                    //currently this undirected version works only for uniformly-coupled networks
					b[u * N + v] += d;
					b[v * N + u] += d;
				}
			}
		}
		float epsu = 0;
		int bkmax = 0, bkavg = 0, Nedges = 0;
		for ( i = 0; i < N; ++i ) {
			for ( j = 0; j < i; ++j ) {
				if ( Aaug[i * N + j] > 0 ) {
					epsu = MAX( epsu,b[i * N + j] * twocell / ( (float) N ) );
					bkavg += b[i * N + j];
					++Nedges;
					bkmax = MAX( b[i * N + j], bkmax );
				}
			}
		}
		for ( i = 0; i < N; ++i ) {
			for ( j = 0; j < i; ++j ) {
				if ( b[i * N + j] >= bkmax && Aaug[i * N + j] > 0 ) {
					reroute_edge[i * N + j] = 1;//reroute if we are at a bottleneck edge
					reroute_edge[j * N + i] = 1;
				}
			}
		}

		return epsu;
	}
}
struct connection_graph_params_t {//parameters for iterating over the queue
	void* qv, *qseq;
	int nbatch;
	volatile float* epsilon_min;
	float* mean_node_unbalance;
	void* qHead0;
	float twocell;
	int N;
	float* Aaug;
	int directed;
	int* qseq_head;
	int* rerouted;
};
void* run_connection_graph_optimization( void* pparms ) {//optimization routine
	struct connection_graph_params_t* parms = pparms;
	void* qv = parms->qv;
	void* qseq = parms->qseq;
	int nbatch = parms->nbatch;
	int* qseq_head = parms->qseq_head;
	volatile float* epsilon_min = parms->epsilon_min;
	float* mean_node_unbalance = parms->mean_node_unbalance;
	float twocell = parms->twocell;
	int N = parms->N;
	float* Aaug = parms->Aaug;
	int diam = N;
	int directed = parms->directed;

	struct path_choice_queue* qHead0 = parms->qHead0;
	struct path_choice_queue* q = qv;
	int* reroute_edge = malloc( N * N * sizeof( int ) );
	int ktoj, itoj, itok;
	while ( q != NULL ) {
		memset( reroute_edge,0,N * N * sizeof( int ) );
		float epsilon = run_connection_graph_method_for_path_choice( q, reroute_edge, mean_node_unbalance, twocell, N, directed, Aaug );//compute our current bound
		epsilon_min[0] = MIN( epsilon_min[0], epsilon );//compare it to our current best bound
		if ( epsilon < 2 * ( epsilon_min[0] ) ) {//this backtracking criterion is optimal in the case of uniformly weighted, 
                                                //node-balanced networks; see the paper for more details.
			int i,j;
			for ( i = 0; i < N; ++i ) {
				for ( j = 0; j < N; ++j ) {
                    
					for ( itoj = 0; itoj < diam && q->all_pairs_paths[( i * N + j ) * diam + itoj] != i; ++itoj ) ;
                    
					if ( itoj == diam ) {
						continue;
					}//if there is no path from i to j we have no way to reroute.
					
					int d;
					int reroute = 0;
					for ( d = 0; d < itoj; ++d ) {//we consider whether we ought to reroute along this path (based on                                
                                                  //whether it passes through a bottleneck edge.
						int ire = q->all_pairs_paths[( i * N + j ) * diam + d];
						int jre = q->all_pairs_paths[( i * N + j ) * diam + d + 1];
						if ( reroute_edge[jre * N + ire] ) {
							reroute = 1;
							break;
						}

					}
					if ( !reroute ) {
						continue;
					}

					int k;
					for ( k = 0; k < N; ++k ) {
                        //our next iteration consists of the concatenated path $P_{ik} + P_{kj}$
                        //compute this new path
						if ( parms->rerouted[i * N * N + j * N + k] ) {
							continue;
						}
						if ( k == i || k == j ) {
							continue;
						}
						for ( itok = 0; itok < diam && q->all_pairs_paths[( i * N + k ) * diam + itok] != i; ++itok ) ;
						for ( ktoj = 0; ktoj < diam && q->all_pairs_paths[( k * N + j ) * diam + ktoj] != k; ++ktoj ) ;
						if ( itok == diam ) {
							continue;
						}
						if ( ktoj == diam ) {
							continue;
						}
						int use = 1;
						for ( d = 0; d < ktoj; ++d ) {
							int ire = q->all_pairs_paths[( k * N + j ) * diam + d];
							int jre = q->all_pairs_paths[( k * N + j ) * diam + d + 1];
						}
						for ( d = 0; d < itok; ++d ) {
							int ire = q->all_pairs_paths[( i * N + k ) * diam + d];
							int jre = q->all_pairs_paths[( i * N + k ) * diam + d + 1];
						}
						if ( !use ) {
							continue;
						}

						if ( !directed && ( N / twocell ) * epsilon_min[0] * 2 <= itoj + ktoj - 1.0000000001 ) {
							continue;
						}

                        //and add it to the queue
						struct path_choice_queue* qHead = alloc_seq( qseq, nbatch,N, qseq_head );
						qHead->next = NULL;

						int kk;
                        int ii,jj;
						for ( ii = 0; ii < N; ++ii ) {
                            for ( jj = 0; jj < N; ++jj) {
                                int m=jj;
                                for ( kk = 1; kk < diam && m!=ii; ++kk) {
                                    m=q->all_pairs_paths[(ii*N+jj)*diam+kk];
                                    qHead->all_pairs_paths[(ii*N+jj)*diam+kk]=m;
                                }
                            }
                        }
						
						for ( kk = 0; kk <= itok; ++kk ) {
                            
                            int m=q->all_pairs_paths[( k * N + j ) * diam + kk];
                            parms->rerouted[i * N * N + j * N + m] = 1;
							qHead->all_pairs_paths[( i * N + j ) * diam + kk + ktoj] = q->all_pairs_paths[( i * N + k ) * diam + kk];
						}
						for ( kk = 0; kk <= ktoj - 1; ++kk ) {
                            int m=q->all_pairs_paths[( k * N + j ) * diam + kk];
                            parms->rerouted[i * N * N + j * N + m] = 1;
							qHead->all_pairs_paths[( i * N + j ) * diam + kk] = q->all_pairs_paths[( k * N + j ) * diam + kk];
						}
						parms->rerouted[i * N * N + j * N + k] = 1;
						//and to the visited configuration list
						qHead->next = q->next;
						struct path_choice_queue* qHead0 = q;
						qHead0->next = qHead;


					}

				}
			}
		}
		//keep iterating until we have nothing left to examine.
		q = q->next;



	}
	free( reroute_edge );
	return NULL;
}

float generalized_connection_graph_method( float* A, float a, int num_nodes, int augment, int nbatch ) {
	int N = num_nodes;
	int diam = N;
	struct path_choice_queue* qseq = malloc( nbatch * sizeof( struct path_choice_queue ) );
	int directed = 0;
	memset( qseq,0,sizeof( struct path_choice_queue ) * nbatch );
	float twocell = a;
	float* unbalance = malloc( N * sizeof( float ) );
	int i,j, k;
	for ( i = 0; i < N; ++i ) {
		for ( j = 0; j < i; ++j ) {
			if ( A[i * N + j] != A[j * N + i] ) {
				directed = 1;
			}
		}
	}
	for ( i = 0; i < N; ++i ) {
		unbalance[i] = 0;
		for ( j = 0; j < N; ++j ) {
			if ( i == j ) {
				continue;
			}
			unbalance[i] += A[i * N + j];
			unbalance[i] -= A[j * N + i];
		}
	}
	float* mean_node_unbalance = NULL;
	float* Aaug = A;
	float* path_weights = NULL;
	if ( directed ) {
		mean_node_unbalance = malloc( N * N * sizeof( float ) );
		Aaug = malloc( N * N * sizeof( float ) );
		path_weights = malloc( N * N * sizeof( float ) );
		for ( i = 0; i < N; ++i ) {
			for ( j = 0; j < N; ++j ) {
				Aaug[i * N + j] = 0.0f;
			}
		}
		for ( i = 0; i < N; ++i ) {
			for ( j = 0; j < N; ++j ) {
				Aaug[i * N + j] = 0.0f;
				if ( i == j ) {
					mean_node_unbalance[i * N + j] = 0;
					Aaug[i * N + j] = 0.0f;
				} else {
					mean_node_unbalance[i * N + j] = ( unbalance[i] + unbalance[j] ) / 2.0f;
					Aaug[i * N + j] = ( A[i * N + j] + A[j * N + i] ) / 2.0;
					if ( mean_node_unbalance[i * N + j] < 0 ) {
						if ( augment || Aaug[i * N + j] != 0 ) {
							Aaug[i * N + j] += fabs( mean_node_unbalance[i * N + j] / N );
						}
					}
					path_weights[i * N + j] =
						MAX( mean_node_unbalance[i * N + j] / a + 1,0 );
				}
			}
		}
		free( unbalance );
	}

	float* dist = malloc( sizeof( float ) * N * N );
	int* pred = malloc( sizeof( int ) * N * N * diam );

    //floyd-warshall pre-initialization
	for ( i = 0; i < N; ++i ) {
		for ( j = 0; j < N; ++j ) {
			for ( k = 0; k < diam; ++k ) {

				pred[( i * N + j ) * diam + k] = -2;
			}
			if ( i != j ) {
				dist[i * N + j] = ( Aaug[i * N + j] > 0 ) ? 1 : N * N;
				if ( Aaug[i * N + j] > 0 ) {
					pred[( i * N + j ) * diam + 0] = i;
					pred[( j * N + i ) * diam + 0] = j;
				} else {
					pred[( i * N + j ) * diam + 0] = -1;
					pred[( j * N + i ) * diam + 0] = -1;
				}
			} else {
				dist[i * N + j] = 0;
			}
		}
	}
	int m,n;
    //floyd-warshall main algorithm
	for ( k = 0; k < N; ++k ) {
		for ( i = 0; i < N; ++i ) {
			for ( j = 0; j < N; ++j ) {
				if ( dist[i * N + j] > dist[i * N + k] + dist[k * N + j] ) {
					dist[i * N + j] = dist[i * N + k] + dist[k * N + j];
					for ( m = 0; m < diam; ++m ) {
						if ( pred[( i * N + j ) * diam + m] < -1 ) {
							break;
						}
						pred[( i * N + j ) * diam + m] = pred[( k * N + j ) * diam + m];
					}
				} else if ( dist[i * N + j] == dist[i * N + k] + dist[k * N + j] )                      {
					for ( m = 0; m < diam; ++m ) {
						if ( pred[( i * N + j ) * diam + m] < -1 ) {
							for ( n = m; n < diam; ++n ) {
								if ( pred[( k * N + j ) * diam + n] < -1 ) {
									break;
								}
								pred[( i * N + j ) * diam + n] = pred[( k * n + j ) * diam + n - m];
							}
							break;
						}
					}
				}
			}
		}
	}
	for ( i = 0; i < N; ++i ) {
		for ( j = 0; j < N; ++j ) {
			if ( dist[i * N + j] >= N * N ) {
				return -1;
			}
		}
	}
	int* rerouted = malloc( N * N * N * sizeof( int ) );
	memset( rerouted,0,N * N * N * sizeof( int ) );
	int* permutation = malloc( N * N * sizeof( int ) );
	memset( permutation,0,N * N * sizeof( int ) );
	int qseq_head = 0;
	struct path_choice_queue* q0;
	build_queue_from_predecessor_matrix( &q0, pred, permutation, dist, N, nbatch, qseq, &qseq_head, Aaug );
	struct path_choice_queue* q1 = q0, *qHead0;
	float epsilon_min = FLT_MAX;
	struct connection_graph_params_t parms =
	{
		q1, qseq,
		nbatch,
		&epsilon_min,
		mean_node_unbalance,
		qHead0,
		twocell,
		N,
		Aaug,
		directed,
		&qseq_head,
		rerouted
	};
    
	run_connection_graph_optimization( &parms );
    
	for ( i = 0; i < nbatch; ++i )
	{
		if ( qseq[i].all_pairs_paths != NULL ) {
			free( qseq[i].all_pairs_paths );
		}
	}
	free( permutation );
	free( pred );
	free( dist );
    free(rerouted);
	if ( directed ) {
		free( path_weights );
		free( Aaug );
		free( mean_node_unbalance );
	}
	free( qseq );
	pred = NULL; dist = NULL;
	Aaug = NULL;
	float result = epsilon_min;
	return result;
}


int main( int argc, char** argv ) { ///example which produces fig. 3 from the augmented graph paper.
                                    //eigenvalue computation is via arpack.
	int N = 100;
	int i,j, k;
	Complex* workd = malloc( 3 * N * sizeof( Complex ) );//"working arrays" for arpack.
	Complex* workl = malloc( ( 3 * N * N + 5 * N ) * sizeof( Complex ) );
	Complex* resid = malloc( N * sizeof( Complex ) );
	Complex* V = malloc( N * N * sizeof( Complex ) );
	float* workr = malloc( N * sizeof( float ) );
	float* Adj = malloc( N * N * sizeof( float ) );
    /*
	for ( k = 5; k <= 50; ++k ) {
            memset( Adj,0,N * N * sizeof( float ) );
            for ( i = 0; i < N; ++i ) {
                for ( j = 0; j < N; ++j ) {
                    if(j%50<k){
                        Adj[i*N+j]=1;
                    }
                }
            }*/
    for ( k = 2; k <= 50; ++k ) {
            memset( Adj,0,N * N * sizeof( float ) );
            for ( i = 0; i < N; ++i ) {
                for ( j = 1; j <=k; ++j ) {
                    if(i%2==0){
                        Adj[i*N+(i+j)%N]=1;
                    }
                    else{
                        Adj[i+((i+j)%N)*N]=1;
                    }
                }
            }
		//printf("\n");
		float* Adj1 = malloc( N * N * sizeof( float ) );
		memcpy( Adj1, Adj, N * N * sizeof( float ) );
		float eps1 = generalized_connection_graph_method( Adj,7.79,N,1,1024 );
        printf( "%i %f ",k,eps1);
		float eps0 = generalized_connection_graph_method( Adj,7.79,N,0,1024 );
		for ( i = 0; i < N; ++i ) {
			Adj1[i] = Adj[i];
			float sum = 0;
			for ( j = 0; j < N; ++j ) {
				sum += Adj1[j * N + i];
			}
			Adj1[i * N + i] = -sum;
		}
		int ido = 0, nev = 97;
		int ncv = N;
		float tol = 0.000001;
		int ldv = N;
		int iparam[11] = {1,0,10000000,1,0,1,1,0,0,0,0};
		int ipntr[14] = {0,N,2 * N,N * 2,0,N * 4,N * 5,N * 5 + N * N, N * 5 + N * N,0,0,0,0,N * N * 2 + N * 5};
		int lworkl = 3 * N * N + 8 * N;
		int info = 0;
		char bmat = 'I';
		char which[2] = {'L','R'};
		while ( 1 ) {
			cnaupd_( &ido, &bmat, &N, which,
					 &nev, &tol, resid,
					 &ncv,  V, &ldv,
					 iparam, ipntr, workd,
					 workl, &lworkl, workr, &info );
			if ( ido == 99 ) {
				break;
			} else if ( ido = 1 || ido == -1 )          {
				workd[i + ipntr[2]][0] = workd[i + ipntr[0]][0];
				workd[i + ipntr[2]][1] = workd[i + ipntr[0]][1];
				for ( i = 0; i < N; ++i ) {
					workd[i + ipntr[1]][0] = 0;
					workd[i + ipntr[1]][1] = 0;
					for ( j = 0; j < N; ++j ) {
						workd[i + ipntr[1]][1] += Adj1[i * N + j] * workd[j + ipntr[0]][0];
						workd[i + ipntr[1]][1] += Adj1[i * N + j] * workd[j + ipntr[0]][1];
					}
				}
			} else if ( ido == 2 )        {

				for ( i = 0; i < N; ++i ) {
					workd[i + ipntr[1]][0] = workd[i + ipntr[0]][0];
					workd[i + ipntr[1]][1] = workd[i + ipntr[0]][1];
				}
			}
		}
		free(Adj1);
		float re_eig2 = workl[ipntr[5] + 1][0];
		int components = 0;
		 printf( "%f %f %f\n", eps0,
				7.79 / fabs( re_eig2 ), re_eig2 );
        fflush( stdout );
	}
	free(Adj);
    free(V);
    free(workd);
    free(workl);
    free(workr);
    free(resid);
	exit( 0 );
}
