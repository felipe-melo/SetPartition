#include <cstdio>
#include <cstdlib>
#include <pthread.h>
#include <vector>
#include <semaphore.h>
#include <pthread.h>
#include "App.h"
#define GENERATE_LP_FILE
//#define DBGSOL
#define INTEGER_COSTS
#define DUAL_ASCENT
//#define UNITARY_ORLIB

using namespace std;

#ifdef INTEGER_COSTS
const double DiffLowUp = 0.9999;
#else
const double DiffLowUp = 0.0001;
#endif

const int MaxLevelLog = 3;

const int NumMajorIterRoot = 10;

const int NumMajorIterNodes = 5;

const double MaxLBFracRoot = 0.5;

const double MaxLBFracNodes = 0.3;

const double StepLBFrac = 0.7;

const double Infinity = 1e+15;

const int MaxHashedCols = 1000;

double upperBound;

#ifdef DBGSOL
const int dbgsol[] = { 2, 10, 18, 27, 42, 43, 48, 49 };
//const int dbgsol[] = { 41, 32, 44, 43 };
//const int dbgsol[] = { 139, 165, 495, 249, 248, 295, 442, 98, 331, 39,
//    259, 118, 120, 443, 446, 457, 213, 89, 303, 102, 103, 445, 21,
//    97, 415, 200, 366, 417 };
//const int dbgsol[] = {  24, 39, 55, 296, 12, 27, 246, 252, 68, 132, 405,
//    489, 241, 375, 174, 471, 20, 453, 89, 19, 218, 417, 190, 71, 115,
//    346, 415, 21, 129, 70, 214 };
vector<bool> dbginsol;
#endif

#ifdef GENERATE_LP_FILE
char lpname[100];
#endif

class BBNode;

typedef struct Element Element;
typedef struct Stack Stack;

struct Element{
	BBNode *child;
    int nodeCount;
    double acumPerc;
    double chPerc;
    int id;
};

struct Stack {
    BBNode *value;
    Stack *next;
};

Element *nodeVetor;

sem_t mutexUpperBound;
sem_t *mutexStack;

int index;
int quantThreads;
bool isFirst;

Stack **load;

int *stackSize;

Stack *push(Stack *stack, BBNode *value);
bool isEmpty(Stack *stack);

// find a value in a sorted array
bool find( int v, int* a, int a_size ) {
    int l = 0, r = a_size - 1;
    while (r >= l)
    {
        int m = (r + l)/2;
        if (v == a[m])
            return true;
        else if (v < a[m])
            r = m - 1;
        else
            l = m + 1;
    }
    return false;
}

// merge two sorted arrays
int merge( int* res, int* a, int* b, int a_size, int b_size ) {
    int i = 0, j = 0;
    int sz = 0;
    while ((i < a_size) && (j < b_size))
    {
        if (a[i] == b[j])
        {
            if (res != NULL) res[sz] = j;
            sz++;
            i++;
            j++;
        }
        else if (a[i] < b[j])
            i++;
        else
            j++;
    }
    return sz;
}

class BBNode
{
public:
    // constructor for the original instance (root node)
    //*************************************************************
    // Construtor do no inicial da arvore. Le arquivo de isntancias
    // e armazena a primeira solucao.
    //*************************************************************
    BBNode( FILE* f )
    {
        bool orlib = (getenv( "SP_ORLIB" ) != NULL);

        // read the number of items and sets
        fprintf(stderr, "Reading instance...\n" );
        int n = 0, m = 0;
        fscanf( f, "%d %d", &n, &m );
        numCols = numSets = m;
        numRows = n;
        vector<int> nonFixed_;
        vector<double> costs_;
        vector< vector<int> > rows_;
        vector<int> fixedSets_;
        vector< vector<int> > cols_;
        vector<int> origRows_;
        nonFixed_.resize( m );
        costs_.resize( m );
        rows_.resize( n );
        level = 0;

#ifdef DBGSOL
        int k = sizeof(dbgsol)/sizeof(int);
        dbginsol.resize(m, false);
        for (int i = 0; i < k; i++)
            dbginsol[dbgsol[i]] = true;
#endif

        // read the set costs
        lowerBound = 0.0;
        for (int j = 0; j < m; j++)
        {
            fscanf( f, "%lf", &(costs_[j]) );
            nonFixed_[j] = j;

            if (orlib)
            {
#ifdef UNITARY_ORLIB
                costs_[j] = 1.0;
#endif
                int k = 0;
                fscanf( f, "%d", &k );
                vector<int> col(k, 0);

                // read each element of the current column
                for (int i = 0; i < k; i++)
                {
                    fscanf( f, "%d", &(col[i]) );
                    col[i]--;
                    int ii = i;
                    while (ii > 0)
                    {
                        if (col[ii] == col[ii-1])
                        {
                            fprintf(stderr, "Error in the %dth element "
                                    "of col %d\n", i+1, j );
                            throw -29832;
                        }
                        if (col[ii] < col[ii-1])
                        {
                            int aux = col[ii];
                            col[ii] = col[ii-1];
                            col[ii-1] = aux;
                            ii--;
                        }
                        else
                            break;
                    }
                }

                // add the elements to the rows
                for (int i = 0; i < k; i++)
                    rows_[col[i]].push_back(j);
            }
        }

        if (!orlib)
        {
            // read each row (sets that contain each item)
            for (int i = 0; i < n; i++)
            {
                int k = 0;
                fscanf( f, "%d", &k );
                if (k >= 0)
                {
                    rows_[i].resize( k );

                    // read each element of the current row
                    for (int j = 0; j < k; j++)
                    {
                        fscanf( f, "%d", &(rows_[i][j]) );
                        int jj = j;
                        while (jj > 0)
                        {
                            if (rows_[i][jj] == rows_[i][jj-1])
                            {
                                fprintf(stderr, "Error in the %dth element"
                                        " of row %d\n", j+1, i );
                                throw -29832;
                            }
                            if (rows_[i][jj] < rows_[i][jj-1])
                            {
                                int aux = rows_[i][jj];
                                rows_[i][jj] = rows_[i][jj-1];
                                rows_[i][jj-1] = aux;
                                jj--;
                            }
                            else
                                break;
                        }
                    }
                }
                else
                {
                    // read each element of the current row
                    int j = 0;
                    fscanf( f, "%d", &j );
                    while (j != -1)
                    {
                        if ((j < 0) || (j >= m))
                        {
                            fprintf(stderr, "Error in the %dth element"
                                    " of row %d\n", rows_[i].size()+1, i );
                            throw -29832;
                        }
                        if (rows_[i].size() != 0)
                            if (rows_[i].back() >= j)
                            {
                                fprintf(stderr, "Error in the %dth element"
                                        " of row %d\n", rows_[i].size()+1, i );
                                throw -29832;
                            }
                        rows_[i].push_back(j);
                        fscanf( f, "%d", &j );
                    }
                }
            }
        }

        // compute the columns and the hash values
        int numOnes = 0;
        cols_.resize( m );
        vector<int> rowHashValues( n );
        origRows_.resize( n );
        int maxRowSize = 0;
        for (int i = 0; i < n; i++)
        {
            rowHashValues[i] = unsigned(rand() + rand() * RAND_MAX) % MaxHashedCols;
            origRows_[i] = i;
            for (int j = 0; j < (int)rows_[i].size(); j++)
            {
                cols_[rows_[i][j]].push_back( i );
                numOnes++;
            }
            if (maxRowSize < (int)rows_[i].size())
                maxRowSize = rows_[i].size();
        }

#ifdef GENERATE_LP_FILE
        FILE* lp = fopen( lpname, "wt" );
        if (lp != NULL)
        {
            fprintf( lp, "Minimize\nobj:" );
            for (int j = 0; j < m; j++)
            {
                if (j > 0) fprintf( lp, " +" );
                fprintf( lp, " %g x_%d", costs_[j], j );
            }
            fprintf( lp, "\nSubject To\n" );
            for (int i = 0; i < n; i++)
            {
                fprintf( lp, "r%d:", i );
                for (int j = 0; j < (int)rows_[i].size(); j++)
                {
                    if (j > 0) fprintf( lp, " +" );
                    fprintf( lp, " x_%d", rows_[i][j] );
                }
                fprintf( lp, " = 1\n" );
            }
            fprintf( lp, "Binaries\n" );
            for (int j = 0; j < m; j++)
                fprintf( lp, " x_%d\n", j );
            fprintf( lp, "\nEnd\n" );
            fclose(lp);
        }
        //exit(0);
#endif

        // compute the columns and remove the dominated ones
        fprintf(stderr, "%d items, %d sets, %5.3lf%c of ones\n"
                "Preprocessing instance...\n",
                n, m, double(numOnes)/double(m*n), '%' );
        vector< vector<int> > colHash;
        colHash.resize(MaxHashedCols);
        for (int j = 0; j < m; j++)
        {
            // add the current column to the hash table
            int hash = 0;
            for (int i = 0; i < (int)cols_[j].size(); i++)
                hash = (hash + rowHashValues[cols_[j][i]]) % MaxHashedCols;
            colHash[hash].push_back( j );
        }
        int removed = 0;
        for (int j = 0; j < m; j++)
        {
            // check for empty columns
            if (cols_[j].size() == 0)
            {
                costs_[j] = Infinity;
                removed++;
                continue;
            }

            // calculate the hash address
            int hash = 0;
            for (int i = 0; i < (int)cols_[j].size(); i++)
                hash = (hash + rowHashValues[cols_[j][i]]) % MaxHashedCols;

            // check for repeated columns
            for (int k = 0; k < (int)colHash[hash].size(); k++)
            {
                int kk = colHash[hash][k];
                if (kk >= j) break;
                if (costs_[kk] == Infinity) continue;
                if (cols_[kk] == cols_[j])
                {
                    //fprintf(stderr, "Columns %d and %d are the same set!\n", k, j );
                    if (costs_[kk] > costs_[j])
                        costs_[kk] = Infinity;
                    else
                        costs_[j] = Infinity;
                    removed++;
                    break;
                }
            }
        }
        fprintf(stderr, "%d removed sets.\nCreating root node data...", removed );
        buffer = malloc(    n*sizeof(double) +          // minRow
                            m*sizeof(double) +          // saveCosts
                            m*sizeof(double) +          // costs
                            n*sizeof(int) +             // parent2child
                            m*sizeof(int) +             // setSizes
                            n*sizeof(int) +             // newSat
                            n*sizeof(int) +             // backdir
                            maxRowSize*sizeof(int) +    // branch
                            m*sizeof(int) +             // nonFixed
                            n*sizeof(int*) +
                            numOnes*sizeof(int) +       // rows
                            n*sizeof(int) +             // rows_size
                            m*sizeof(int) +             // compat
                            sizeof(int) +               // fixedSets
                            m*sizeof(int*) +
                            numOnes*sizeof(int) +       // cols
                            m*sizeof(int) +             // cols_size
                            n*sizeof(int) +             // origRows
                            m*sizeof(bool) +            // isCompat
                            n*sizeof(bool)              // isSat
                       );
        char* ptr = (char*)buffer;
        minRow = (double*)ptr;
        ptr += n*sizeof(double);
        saveCosts = (double*)ptr;
        ptr += m*sizeof(double);
        costs = (double*)ptr;
        ptr += m*sizeof(double);
        for (int j = 0; j < m; j++) costs[j] = costs_[j];
        parent2child = (int*)ptr;
        ptr += n*sizeof(int);
        setSizes = (int*)ptr;
        ptr += m*sizeof(int);
        newSat = (int*)ptr;
        ptr += n*sizeof(int);
        backdir = (int*)ptr;
        ptr += n*sizeof(int);
        branch = (int*)ptr;
        ptr += maxRowSize*sizeof(int);
        nonFixed = (int*)ptr;
        ptr += m*sizeof(int);
        for (int j = 0; j < m; j++) nonFixed[j] = nonFixed_[j];
        rows = (int**)ptr;
        ptr += n*sizeof(int*);
        for (int i = 0; i < n; i++)
        {
            rows[i] = (int*)ptr;
            ptr += (rows_[i].size())*sizeof(int);
            for (int j = 0; j < (int)rows_[i].size(); j++)
                rows[i][j] = rows_[i][j];
        }
        rows_size = (int*)ptr;
        ptr += n*sizeof(int);
        for (int i = 0; i < n; i++) rows_size[i] = rows_[i].size();
        compat = (int*)ptr;
        ptr += m*sizeof(int);
        fixedSets = (int*)ptr;
        ptr += sizeof(int);
        fixedSets_size = 0;
        cols = (int**)ptr;
        ptr += m*sizeof(int*);
        ptr += numOnes*sizeof(int);
        cols_size = (int*)ptr;
        ptr += m*sizeof(int);
        for (int j = 0; j < m; j++) cols_size[j] = cols_[j].size();
        origRows = (int*)ptr;
        ptr += n*sizeof(int);
        for (int i = 0; i < n; i++) origRows[i] = origRows_[i];
        isCompat = (bool*)ptr;
        ptr += m*sizeof(bool);
        isSat = (bool*)ptr;
        fprintf(stderr, " done!\n" );
    }

    // constructor for a child node that fixes a given set
    //*************************************************************
    // Construtor dos nos filhos dixando um dado conjunto
    //*************************************************************
    BBNode( BBNode& parent, int fset) {
        //fprintf(stderr, "Fixing set %d...\n", fset);

        {
            // compute the compatibilities only for the branching set
            int m = parent.numCols;
            int n = parent.numRows;
            for (int j = 0; j < m; j++)
                parent.cols_size[j] = 0;
            for (int i = 0; i < n; i++) {
                for (int jj = 0; jj < parent.rows_size[i]; jj++) {
                    int j = parent.rows[i][jj];
                    parent.cols[j][(parent.cols_size[j])++] = i;
                }
            }
            for (int j = 0; j < m; j++) parent.isCompat[j] = true;
            for (int ii = 0; ii < parent.cols_size[fset]; ii++)
            {
                // set the non-compatibilities
                int i = parent.cols[fset][ii];
                for (int k = 0; k < parent.rows_size[i]; k++)
                    parent.isCompat[parent.rows[i][k]] = false;
            }

            // save the computed compatibilites
            int count = 0;
            for (int k = 0; k < m; k++)
                if (parent.isCompat[k])
                {
                    parent.compat[count] = k;
                    count++;
                }
            parent.compat_size = count;
        }

        // calculate the number of columns, rows and ones
        int numOnes = 0;
        int maxRowSize = 0;
        int m = this->numCols = parent.compat_size;
        this->numRows = 0;
        for (int i = 0; i < parent.numRows; i++)
        {
            if (find(fset, parent.rows[i], parent.rows_size[i])) continue;
            this->numRows++;
            int rowSize = merge( NULL, parent.rows[i], parent.compat,
                    parent.rows_size[i], parent.compat_size );
            numOnes += rowSize;
            if (maxRowSize < rowSize) maxRowSize = rowSize;
        }
        int n = this->numRows;

        // allocat memory for all vectors
        int numFixed = parent.fixedSets_size + 1;
        this->buffer = malloc(  n*sizeof(double) +          // minRow
                                m*sizeof(double) +          // saveCosts
                                m*sizeof(double) +          // costs
                                n*sizeof(int) +             // parent2child
                                m*sizeof(int) +             // setSizes
                                n*sizeof(int) +             // newSat
                                n*sizeof(int) +             // backdir
                                maxRowSize*sizeof(int) +    // branch
                                m*sizeof(int) +             // nonFixed
                                n*sizeof(int*) +
                                numOnes*sizeof(int) +       // rows
                                n*sizeof(int) +             // rows_size
                                m*sizeof(int) +             // compat
                                numFixed*sizeof(int) +      // fixedSets
                                m*sizeof(int*) +
                                numOnes*sizeof(int) +       // cols
                                m*sizeof(int) +             // cols_size
                                n*sizeof(int) +             // origRows
                                m*sizeof(bool) +            // isCompat
                                n*sizeof(bool)              // isSat
                             );
        char* ptr = (char*)buffer;
        this->minRow = (double*)ptr;
        ptr += n*sizeof(double);
        this->saveCosts = (double*)ptr;
        ptr += m*sizeof(double);
        this->costs = (double*)ptr;
        ptr += m*sizeof(double);
        this->parent2child = (int*)ptr;
        ptr += n*sizeof(int);
        this->setSizes = (int*)ptr;
        ptr += m*sizeof(int);
        this->newSat = (int*)ptr;
        ptr += n*sizeof(int);
        this->backdir = (int*)ptr;
        ptr += n*sizeof(int);
        this->branch = (int*)ptr;
        ptr += maxRowSize*sizeof(int);
        this->nonFixed = (int*)ptr;
        ptr += m*sizeof(int);
        this->rows = (int**)ptr;
        ptr += n*sizeof(int*);
        ptr += numOnes*sizeof(int);
        this->rows_size = (int*)ptr;
        ptr += n*sizeof(int);
        this->compat = (int*)ptr;
        ptr += m*sizeof(int);
        this->fixedSets = (int*)ptr;
        ptr += numFixed*sizeof(int);
        this->cols = (int**)ptr;
        ptr += m*sizeof(int*);
        ptr += numOnes*sizeof(int);
        this->cols_size = (int*)ptr;
        ptr += m*sizeof(int);
        this->origRows = (int*)ptr;
        ptr += n*sizeof(int);
        this->isCompat = (bool*)ptr;
        ptr += m*sizeof(bool);
        this->isSat = (bool*)ptr;

        // copy the costs and set the fixed sets and cols matrix
        this->lowerBound = parent.lowerBound + parent.costs[fset];
        for (int j = 0; j < m; j++)
            this->costs[j] = parent.costs[parent.compat[j]];
        for (int k = 0; k < parent.fixedSets_size; k++)
            this->fixedSets[k] = parent.fixedSets[k];
        this->fixedSets[parent.fixedSets_size] = parent.nonFixed[fset];
        this->fixedSets_size = numFixed;

        // merge the rows with the compatibilities of the fixed set
        int i = 0;
        ptr = (char*)this->rows;
        ptr += n*sizeof(int*);
        for (int ii = 0; ii < parent.numRows; ii++) {
            parent.parent2child[ii] = -1;
            if (find(fset, parent.rows[ii], parent.rows_size[ii])) continue;
            this->rows[i] = (int*)ptr;
            int sz = merge( this->rows[i], parent.rows[ii], parent.compat,
                    parent.rows_size[ii], parent.compat_size );
            ptr += sz * sizeof(int);
            this->rows_size[i] = sz;
            this->origRows[i] = parent.origRows[ii];
            parent.parent2child[ii] = i;
            i++;
        }

        // calculate the number of useful sets (columns)
        this->numSets = 0;
        for (int j = 0; j < m; j++)
        {
            if (this->lowerBound + this->costs[j] > upperBound - DiffLowUp)
                continue;
            this->numSets++;
        }

        // set the array of non-fixed sets
        for (int j = 0; j < m; j++)
            this->nonFixed[j] = parent.nonFixed[parent.compat[j]];

        // set the level
        this->level = parent.level + 1;
    }

    ~BBNode() {
        free(buffer);
    }

    // solve the problem via branch-and-bound
    //*************************************************************
    // Metodo usado para computar o no. Ao final do metodo uma solucao 
    // pode ser encontrada e nao serao gerados filhos ou a execucao
    // do no podera gerar outros nos filhos. A quantidade de nos geradas
    // nao e previamente conhecida somente, apos a computacao 
    //*************************************************************
    int solve(double solvedPerc, double currPerc, int id) {
        char* ptr;
        // check for feasibility or infeasibility
        if (numSets == 0) {
            if (numRows == 0) {                
                // found a new feasible solution
                fprintf(stderr,"\nFEASIBLE SOLUTION WITH COST %g FOUND:\n", lowerBound);
                for (int j = 0; j < fixedSets_size; j++)
                    fprintf(stderr," %d", fixedSets[j]);
                fprintf(stderr,"\n\nLevel %d: %5.1lf%c solved.\n", level, solvedPerc + currPerc, '%' );
                upperBound = lowerBound;
            } else {
                if (level <= MaxLevelLog)
                    fprintf(stderr, "Level %d: %5.1lf%c solved, Infeasible!\n", level, solvedPerc + currPerc, '%' );
            }
            return 1;
        }

#ifdef DUAL_ASCENT
        // update the lower bound
        double currLBFrac = (level == 0)? MaxLBFracRoot: MaxLBFracNodes;
        double saveLB = -1.0;
        int NumMajorIter = (level == 0)? NumMajorIterRoot: NumMajorIterNodes;
        for (int t = 0; t < NumMajorIter; t++) {
            int numSat = 0;
            for (int i = 0; i < numRows; i++) isSat[i] = false;
            int tt = 0;
            while (numSat < numRows) {
                // compute the non-saturated sets
                for (int j = 0; j < numCols; j++) setSizes[j] = 0;
                for (int i = 0; i < numRows; i++) {
                    if (isSat[i]) continue;
                    for (int j = 0; j < rows_size[i]; j++) {
                        if (costs[rows[i][j]] == Infinity) continue;
                        if (setSizes[rows[i][j]] == 0) cols_size[rows[i][j]] = 0;
                        setSizes[rows[i][j]]++;
                    }
                }
                ptr = (char*)cols;
                ptr += numCols*sizeof(int*);
                for (int j = 0; j < numCols; j++) {
                    cols[j] = (int*)ptr;
                    ptr += setSizes[j]*sizeof(int);
                }
                for (int i = 0; i < numRows; i++) {
                    if (isSat[i]) continue;
                    for (int j = 0; j < rows_size[i]; j++)
                    {
                        if (costs[rows[i][j]] == Infinity) continue;
                        cols[rows[i][j]][cols_size[rows[i][j]]] = i;
                        cols_size[rows[i][j]]++;
                    }
                }

                // compute the row prices
                for (int i = 0; i < numRows; i++) minRow[i] = Infinity;
                for (int i = 0; i < numRows; i++) {
                    // skip the saturated rows
                    if (isSat[i]) continue;

                    // consider the distribution of the current cost
                    for (int j = 0; j < rows_size[i]; j++) {
                        if (costs[rows[i][j]] == Infinity) continue;
                        double icost = costs[rows[i][j]] /
                                double(setSizes[rows[i][j]]);
                        if (minRow[i] > icost) minRow[i] = icost;
                    }
                    lowerBound += minRow[i];
                }
                //fprintf(stderr, "NewLB = %g\n", lowerBound );

                //update the set costs discounting the lower bound
                newSat_size = 0;
                for (int i = 0; i < numRows; i++) {
                    if (isSat[i]) continue;
                    for (int j = 0; j < rows_size[i]; j++) {
                        int jj = rows[i][j];
                        if (costs[jj] == Infinity) continue;
                        costs[jj] -= minRow[i];
                        if (costs[jj] < 0.0001)
                            newSat[newSat_size++] = jj;
                    }
                }
                for (int j = 0; j < newSat_size; j++)
                {
                    int jj = newSat[j];
                    for (int ii = 0; ii < cols_size[jj]; ii++)

                    {
                        int iii = cols[jj][ii];
                        if (!isSat[iii]) numSat++;
                        isSat[iii] = true;
                    }
                }

                // stop if the upper bound has been reached
                if (lowerBound > upperBound - DiffLowUp) break;
                tt++;
                if (tt > 100)
                {
                    //fprintf(stderr,"nonSats = %d\n", numRows - numSat);
                    for (int i = 0; i < numRows; i++)
                    {
                        if (isSat[i]) continue;
                        fprintf(stderr,"row %d:", i);
                        for (int j = 0; j < rows_size[i]; j++)
                        {
                            int jj = rows[i][j];
                            fprintf(stderr,"  cost_%d=%g", jj, costs[jj]);
                        }
                        fprintf(stderr,"\n");
                    }
                    exit(1);
                }
            }
            //fprintf(stderr, "NewLB = %g (saveLB = %g)\n", lowerBound, saveLB );

            // restore the previous lower bound if necessary
            if (saveLB > lowerBound) {
                lowerBound = saveLB;
                for (int j = 0; j < numCols; j++)
                    costs[j] = saveCosts[j];
            }

            // stop if the upper bound has been reached
            if (lowerBound > upperBound - DiffLowUp) break;

            if (t == 0) {
                // fix the columns that are the only ones in a row
                for (int i = 0; i < numRows; i++)
                    if (rows_size[i] == 1)
                    {
                        {
                            // compute the set columns
                            for (int j = 0; j < numCols; j++) cols_size[j] = 0;
                            for (int i = 0; i < numRows; i++)
                                for (int j = 0; j < rows_size[i]; j++)
                                    cols_size[rows[i][j]]++;
                            ptr = (char*)cols;
                            ptr += numCols*sizeof(int*);
                            for (int j = 0; j < numCols; j++)
                            {
                                cols[j] = (int*)ptr;
                                ptr += cols_size[j]*sizeof(int);
                                cols_size[j] = 0;
                            }
                            for (int i = 0; i < numRows; i++)
                                for (int j = 0; j < rows_size[i]; j++)
                                    cols[rows[i][j]][cols_size[j]++] = i;
                        }

                        if (level <= MaxLevelLog)
                            fprintf(stderr, "Level %d: fixing set %d\n", level,
                                   nonFixed[rows[i][0]] );
                        level--;
                        BBNode simple( *this, rows[i][0]);
                        return simple.solve(solvedPerc, currPerc, id);
                    }
            }

            if (t + 1 < NumMajorIter)
            {
                // compute the dual backward direction and length
                for (int i = 0; i < numRows; i++) backdir[i] = -1;
                int countBack = 0;
                for (int i = 0; i < numRows; i++)
                {
                    for (int j = 0; j < rows_size[i]; j++)
                        if (costs[rows[i][j]] < 0.0001)
                            backdir[i]++;
                    countBack += backdir[i];
                    //fprintf(stderr,"back_%d = %d\n", i, backdir[i]);
                }

                if (countBack == 0) break;

                // compute the move size
                double moveSize = 0.0;
                for (int i = 0; i < numRows; i++)
                {
                    if (backdir[i] > 0) continue;
                    for (int j = 0; j < rows_size[i]; j++)
                    {
                        if (costs[rows[i][j]] == Infinity) continue;
                        moveSize += costs[rows[i][j]] / double(rows_size[i]);
                    }
                }

                if (moveSize == 0.0) break;

                // save the state and move the dual back
                saveLB = lowerBound;
                for (int j = 0; j < numCols; j++)
                    saveCosts[j] = costs[j];
                double move = moveSize * currLBFrac;
                //fprintf(stderr,"move = %g (frac = %g)\n", move, currLBFrac);
                for (int i = 0; i < numRows; i++)
                {
                    double change = move * double(backdir[i]) /
                            double(countBack);
                    for (int j = 0; j < rows_size[i]; j++)
                    {
                        if (costs[rows[i][j]] == Infinity) continue;
                        costs[rows[i][j]] += change;
                    }
                    lowerBound -= change;
                }

                // update the move length
                currLBFrac *= StepLBFrac;
            }
        }
        //exit(0);
#endif

        // check if the upper bound has been reached
        
        if (lowerBound > upperBound - DiffLowUp)
        {
            if (level <= MaxLevelLog)
                fprintf(stderr, "Level %d: %5.1lf%c solved, Fathomed by dual ascent!\n",
                        level, solvedPerc + currPerc, '%' );
            return 1;
        }

        // compute the set columns
        for (int j = 0; j < numCols; j++) cols_size[j] = 0;
        for (int i = 0; i < numRows; i++)
            for (int j = 0; j < rows_size[i]; j++)
                cols_size[rows[i][j]]++;
        ptr = (char*)cols;
        ptr += numCols*sizeof(int*);
        for (int j = 0; j < numCols; j++)
        {
            cols[j] = (int*)ptr;
            ptr += cols_size[j]*sizeof(int);
            cols_size[j] = 0;
        }
        for (int i = 0; i < numRows; i++)
            for (int j = 0; j < rows_size[i]; j++)
                cols[rows[i][j]][cols_size[rows[i][j]]++] = i;

        // compute and check dynamic programing lower bounds
        double dpLB = lowerBound;

        // find the best branching row
        int bestCount = 1000000000;
        int bestRow = 0;

        {
            for (int i = 0; i < numRows; i++)
            {
                int count = 0;
                for (int j = 0; j < rows_size[i]; j++)
                {
                    int jj = rows[i][j];

                    // skip the fathomed columns
                    if (lowerBound + costs[jj] > upperBound  - DiffLowUp)
                        continue;

                    //count++;
                    count += (numRows - cols_size[jj]);
                }
                if (count < bestCount)
                {
                    bestCount = count;
                    bestRow = i;
                }
            }
        }

        // print the branching statistics
        if (level <= MaxLevelLog)
            fprintf(stderr, "Level %d: %5.1lf%c solved, LB = %g(%g),"
                    " Branching on %d to %d(%d).\n", level, solvedPerc, '%',
                    lowerBound, dpLB, origRows[bestRow],
                    rows_size[bestRow], bestCount );

        // do the branching
        //*************************************************************
        // Cria vetor (barnch) com os valores dos novos filhos
        //*************************************************************        
        
        int nodeCount = 1;
        double acumPerc = solvedPerc;
        for (int j = 0; j < rows_size[bestRow]; j++)
            branch[j] = rows[bestRow][j];
        branch_size = rows_size[bestRow];
        for (int j = 0; j < branch_size; j++)
        {
            // find the columns with the smallest cost
            for (int jj = j+1; jj < branch_size; jj++)
#ifdef DBGSOL
                if (dbginsol[nonFixed[branch[jj]]] &&
                        !dbginsol[nonFixed[branch[j]]])
#else
                if (costs[branch[jj]] / double(numRows - cols_size[branch[jj]])
                        > costs[branch[j]] / double(numRows - cols_size[branch[j]])) //mudamos a ordem
#endif
                {
                    int aux = branch[j];
                    branch[j] = branch[jj];
                    branch[jj] = aux;
                }

            // skip the fathomed columns
            if (lowerBound + costs[branch[j]] > upperBound  - DiffLowUp)
                continue;
            //*************************************************************
            // Constroi o no filho baseado no valor contido em branch 
            // (valor do conjunto que será fixado) e chama o metodo solve
            // para solucionar o no.
            // Aqui acontece a recursao de execução da árvore. Para paralelizar
            // é necessário que esta recursão seja retirada. Ou seja, 
            // Você poderá criar os nos mas ao invés de chamar o método, pode 
            // armazená-los em um vetor, para que estes sejam distribuídos entres
            // as threads.
            //*************************************************************    

            BBNode *child = new BBNode(*this, branch[j]);

            if (isFirst){
                //printf("Criando filho %d.\n", index);
                /*double chPerc = currPerc / double(branch_size);
                nodeCount += child.solve(upperBound, acumPerc, chPerc );
                acumPerc += chPerc;*/

                /*Element *element = (Element*) malloc(sizeof(Element));
                element->child = child;
                element->chPerc = currPerc / double(branch_size);
                element->acumPerc = solvedPerc + currPerc;
                element->nodeCount = nodeCount+1;
                nodeVetor[index++] = *element;*/
                if (index < quantThreads){
                    load[index] = push(load[index], child);
                    index++;
                }else{
                    index = 0;
                    load[index] = push(load[index], child);
                    index++;
                }
            }else{
                sem_wait(&mutexStack[id]);
                load[id] = push(load[id], child);
                sem_post(&mutexStack[id]);
            }
        }

        isFirst = false;

        // print the node statistics
        if (level <= MaxLevelLog) {
            fprintf(stderr, "Level %d: %5.1lf%c solved, Solved in %d nodes.\n", level, solvedPerc + currPerc, '%', nodeCount );
        }
        return nodeCount;
    }

    int solveRec(double solvedPerc, double currPerc, int id ) {
        char* ptr;

        // check for feasibility or infeasibility
        if (numSets == 0)
        {
            if (numRows == 0)
            {
                // found a new feasible solution
                fprintf(stderr,"\nFEASIBLE SOLUTION WITH COST %g FOUND:\n", lowerBound);
                for (int j = 0; j < fixedSets_size; j++)
                    fprintf(stderr," %d", fixedSets[j]);
                fprintf(stderr,"\n\nLevel %d: %5.1lf%c solved.\n", level,
                        solvedPerc + currPerc, '%' );
                sem_wait(&mutexUpperBound);
                upperBound = lowerBound;
                sem_post(&mutexUpperBound);
            }
            else
            {
                if (level <= MaxLevelLog)
                    fprintf(stderr, "Level %d: %5.1lf%c solved, Infeasible!\n", level,
                            solvedPerc + currPerc, '%' );
            }
            return 1;
        }

#ifdef DUAL_ASCENT
        // update the lower bound
        double currLBFrac = (level == 0)? MaxLBFracRoot: MaxLBFracNodes;
        double saveLB = -1.0;
        int NumMajorIter = (level == 0)? NumMajorIterRoot: NumMajorIterNodes;
        for (int t = 0; t < NumMajorIter; t++)
        {
            int numSat = 0;
            for (int i = 0; i < numRows; i++) isSat[i] = false;
            int tt = 0;
            while (numSat < numRows)
            {
                // compute the non-saturated sets
                for (int j = 0; j < numCols; j++) setSizes[j] = 0;
                for (int i = 0; i < numRows; i++)
                {
                    if (isSat[i]) continue;
                    for (int j = 0; j < rows_size[i]; j++)
                    {
                        if (costs[rows[i][j]] == Infinity) continue;
                        if (setSizes[rows[i][j]] == 0) cols_size[rows[i][j]] = 0;
                        setSizes[rows[i][j]]++;
                    }
                }
                ptr = (char*)cols;
                ptr += numCols*sizeof(int*);
                for (int j = 0; j < numCols; j++)
                {
                    cols[j] = (int*)ptr;
                    ptr += setSizes[j]*sizeof(int);
                }
                for (int i = 0; i < numRows; i++)
                {
                    if (isSat[i]) continue;
                    for (int j = 0; j < rows_size[i]; j++)
                    {
                        if (costs[rows[i][j]] == Infinity) continue;
                        cols[rows[i][j]][cols_size[rows[i][j]]] = i;
                        cols_size[rows[i][j]]++;
                    }
                }

                // compute the row prices
                for (int i = 0; i < numRows; i++) minRow[i] = Infinity;
                for (int i = 0; i < numRows; i++)
                {
                    // skip the saturated rows
                    if (isSat[i]) continue;

                    // consider the distribution of the current cost
                    for (int j = 0; j < rows_size[i]; j++)
                    {
                        if (costs[rows[i][j]] == Infinity) continue;
                        double icost = costs[rows[i][j]] /
                                double(setSizes[rows[i][j]]);
                        if (minRow[i] > icost) minRow[i] = icost;
                    }
                    lowerBound += minRow[i];
                }
                //fprintf(stderr, "NewLB = %g\n", lowerBound );

                // update the set costs discounting the lower bound
                newSat_size = 0;
                for (int i = 0; i < numRows; i++)
                {
                    if (isSat[i]) continue;
                    for (int j = 0; j < rows_size[i]; j++)
                    {
                        int jj = rows[i][j];
                        if (costs[jj] == Infinity) continue;
                        costs[jj] -= minRow[i];
                        if (costs[jj] < 0.0001)
                            newSat[newSat_size++] = jj;
                    }
                }
                for (int j = 0; j < newSat_size; j++)
                {
                    int jj = newSat[j];
                    for (int ii = 0; ii < cols_size[jj]; ii++)

                    {
                        int iii = cols[jj][ii];
                        if (!isSat[iii]) numSat++;
                        isSat[iii] = true;
                    }
                }

                // stop if the upper bound has been reached
                if (lowerBound > upperBound - DiffLowUp) break;
                tt++;
                if (tt > 100)
                {
                    fprintf(stderr,"nonSats = %d\n", numRows - numSat);
                    for (int i = 0; i < numRows; i++)
                    {
                        if (isSat[i]) continue;
                        fprintf(stderr,"row %d:", i);
                        for (int j = 0; j < rows_size[i]; j++)
                        {
                            int jj = rows[i][j];
                            fprintf(stderr,"  cost_%d=%g", jj, costs[jj]);
                        }
                        fprintf(stderr,"\n");
                    }
                    exit(1);
                }
            }
            //fprintf(stderr, "NewLB = %g (saveLB = %g)\n", lowerBound, saveLB );

            // restore the previous lower bound if necessary
            if (saveLB > lowerBound)
            {
                lowerBound = saveLB;
                for (int j = 0; j < numCols; j++)
                    costs[j] = saveCosts[j];
            }

            // stop if the upper bound has been reached
            if (lowerBound > upperBound - DiffLowUp) break;

            if (t == 0)
            {
                // fix the columns that are the only ones in a row
                for (int i = 0; i < numRows; i++)
                    if (rows_size[i] == 1)
                    {
                        {
                            // compute the set columns
                            for (int j = 0; j < numCols; j++) cols_size[j] = 0;
                            for (int i = 0; i < numRows; i++)
                                for (int j = 0; j < rows_size[i]; j++)
                                    cols_size[rows[i][j]]++;
                            ptr = (char*)cols;
                            ptr += numCols*sizeof(int*);
                            for (int j = 0; j < numCols; j++)
                            {
                                cols[j] = (int*)ptr;
                                ptr += cols_size[j]*sizeof(int);
                                cols_size[j] = 0;
                            }
                            for (int i = 0; i < numRows; i++)
                                for (int j = 0; j < rows_size[i]; j++)
                                    cols[rows[i][j]][cols_size[j]++] = i;
                        }

                        //if (level <= MaxLevelLog)
                        //    fprintf(stderr, "Level %d: fixing set %d\n", level,
                        //            nonFixed[rows[i][0]] );
                        level--;
                        BBNode simple( *this, rows[i][0]);
                        //printf("Entrou aki\n");
                        return simple.solveRec(solvedPerc, currPerc, id);
                    }
            }

            if (t + 1 < NumMajorIter)
            {
                // compute the dual backward direction and length
                for (int i = 0; i < numRows; i++) backdir[i] = -1;
                int countBack = 0;
                for (int i = 0; i < numRows; i++)
                {
                    for (int j = 0; j < rows_size[i]; j++)
                        if (costs[rows[i][j]] < 0.0001)
                            backdir[i]++;
                    countBack += backdir[i];
                    //fprintf(stderr,"back_%d = %d\n", i, backdir[i]);
                }

                if (countBack == 0) break;

                // compute the move size
                double moveSize = 0.0;
                for (int i = 0; i < numRows; i++)
                {
                    if (backdir[i] > 0) continue;
                    for (int j = 0; j < rows_size[i]; j++)
                    {
                        if (costs[rows[i][j]] == Infinity) continue;
                        moveSize += costs[rows[i][j]] / double(rows_size[i]);
                    }
                }

                if (moveSize == 0.0) break;

                // save the state and move the dual back
                saveLB = lowerBound;
                for (int j = 0; j < numCols; j++)
                    saveCosts[j] = costs[j];
                double move = moveSize * currLBFrac;
                //fprintf(stderr,"move = %g (frac = %g)\n", move, currLBFrac);
                for (int i = 0; i < numRows; i++)
                {
                    double change = move * double(backdir[i]) /
                            double(countBack);
                    for (int j = 0; j < rows_size[i]; j++)
                    {
                        if (costs[rows[i][j]] == Infinity) continue;
                        costs[rows[i][j]] += change;
                    }
                    lowerBound -= change;
                }

                // update the move length
                currLBFrac *= StepLBFrac;
            }
        }
        //exit(0);
#endif

        // check if the upper bound has been reached
        if (lowerBound > upperBound - DiffLowUp)
        {
            if (level <= MaxLevelLog)
                fprintf(stderr, "Level %d: %5.1lf%c solved, Fathomed by dual ascent!\n",
                        level, solvedPerc + currPerc, '%' );
            return 1;
        }

        // compute the set columns
        for (int j = 0; j < numCols; j++) cols_size[j] = 0;
        for (int i = 0; i < numRows; i++)
            for (int j = 0; j < rows_size[i]; j++)
                cols_size[rows[i][j]]++;
        ptr = (char*)cols;
        ptr += numCols*sizeof(int*);
        for (int j = 0; j < numCols; j++)
        {
            cols[j] = (int*)ptr;
            ptr += cols_size[j]*sizeof(int);
            cols_size[j] = 0;
        }
        for (int i = 0; i < numRows; i++)
            for (int j = 0; j < rows_size[i]; j++)
                cols[rows[i][j]][cols_size[rows[i][j]]++] = i;

        // compute and check dynamic programing lower bounds
        double dpLB = lowerBound;

        // find the best branching row
        int bestCount = 1000000000;
        int bestRow = 0;

        {
            for (int i = 0; i < numRows; i++)
            {
                int count = 0;
                for (int j = 0; j < rows_size[i]; j++)
                {
                    int jj = rows[i][j];

                    // skip the fathomed columns
                    if (lowerBound + costs[jj] > upperBound  - DiffLowUp)
                        continue;

                    //count++;
                    count += (numRows - cols_size[jj]);
                }
                if (count < bestCount)
                {
                    bestCount = count;
                    bestRow = i;
                }
            }
        }

        // print the branching statistics
        if (level <= MaxLevelLog)
            fprintf(stderr, "Level %d: %5.1lf%c solved, LB = %g(%g),"
                    " Branching on %d to %d(%d).\n", level, solvedPerc, '%',
                    lowerBound, dpLB, origRows[bestRow],
                    rows_size[bestRow], bestCount );

        // do the branching
        //*************************************************************
        // Cria vetor (barnch) com os valores dos novos filhos
        //*************************************************************        
        
        int nodeCount = 1;
        double acumPerc = solvedPerc;
        for (int j = 0; j < rows_size[bestRow]; j++)
            branch[j] = rows[bestRow][j];
        branch_size = rows_size[bestRow];
        for (int j = 0; j < branch_size; j++)
        {
            // find the columns with the smallest cost
            for (int jj = j+1; jj < branch_size; jj++)
#ifdef DBGSOL
                if (dbginsol[nonFixed[branch[jj]]] &&
                        !dbginsol[nonFixed[branch[j]]])
#else
                if (costs[branch[jj]] / double(numRows - cols_size[branch[jj]])
                        < costs[branch[j]] / double(numRows - cols_size[branch[j]]))
#endif
                {
                    int aux = branch[j];
                    branch[j] = branch[jj];
                    branch[jj] = aux;
                }

            // skip the fathomed columns
            if (lowerBound + costs[branch[j]] > upperBound  - DiffLowUp)
                continue;
            //*************************************************************
            // Constroi o no filho baseado no valor contido em branch 
            // (valor do conjunto que será fixado) e chama o metodo solve
            // para solucionar o no.
            // Aqui acontece a recursao de execução da árvore. Para paralelizar
            // é necessário que esta recursão seja retirada. Ou seja, 
            // Você poderá criar os nos mas ao invés de chamar o método, pode 
            // armazená-los em um vetor, para que estes sejam distribuídos entres
            // as threads.
            //*************************************************************

            BBNode child( *this, branch[j]);
            double chPerc = currPerc / double(branch_size);
            nodeCount += child.solveRec(acumPerc, chPerc, id);
            acumPerc += chPerc;

        }

        // print the node statistics
        if (level <= MaxLevelLog)
        {
            fprintf(stderr, "Level %d: %5.1lf%c solved, Solved in %d nodes.\n", level,
                    solvedPerc + currPerc, '%', nodeCount );
        }
        return nodeCount;
    }

private:
    // array of non fixed columns
    int* nonFixed;

    // array of set costs
    double* costs;

    // set-partitioning rows: each row is an item represented by an array of
    // all sets that contain it
    int numRows;
    int** rows;
    int* rows_size;

    // for some set, compat gives an array of compatible sets (whose
    // intersection is empty.
    int* compat;
    int compat_size;

    // lower bound for this node
    double lowerBound;

    // array of fixed sets in the branch-and-bound tree
    int* fixedSets;
    int fixedSets_size;

    // number of active sets
    int numSets;

    // matrix of columns
    int numCols;
    int** cols;
    int* cols_size;

    // level in the branch-and-bound tree
    int level;

    // vector of original row indices
    int* origRows;

    // pointer to memory buffer used by all vectors
    void* buffer;

    // local vectors used inside methods
    bool* isCompat;
    int* parent2child;
    double* saveCosts;
    bool* isSat;
    int* setSizes;
    double* minRow;
    int* newSat; int newSat_size;
    int* backdir;
    int* branch; int branch_size;
};

void *run(void *args);

Stack *startStack();
BBNode *pop(Stack **stack);

int main(int argc, char* argv[]) {

	nodeVetor = (Element*) malloc(sizeof(Element) * 500000);
	bool parallel = atoi(argv[2]) == 1 ? true : false;
    isFirst = true;
    
    // read the input data
    if ((argc < 2) || (argc > 4)) {
        fprintf(stderr, "use: BBSP <input filename> [ <upper bound> ]\n" );
        return 1;
    }
    FILE* f = fopen(argv[1], "rt" );
    if (f == NULL) {
        fprintf(stderr, "Fail to open file %s for reading\n", argv[1] );
        return 2;
    }

    sem_init(&mutexUpperBound, 0, 1);  // inicializa

    double ub = Infinity;
    if (argc == 5) sscanf(argv[4], "%lf", &ub );

    // build initialize the RNG
    srand(123456);

    upperBound = ub;

    // read the input file (and convert to an LP file)
#ifdef GENERATE_LP_FILE
    sprintf(lpname, "l%s.lp", argv[1]);
#endif
    BBNode root( f );
    fclose(f);

    // solve the problem
    index = 0;

    if (parallel){
        quantThreads = atoi(argv[3]);
        load = (Stack**) malloc(sizeof(Stack*) * quantThreads);
        mutexStack = (sem_t*) malloc(sizeof(sem_t) * quantThreads);

        for (int i = 0; i < quantThreads; i++){
            load[i] = startStack();
            sem_init(&mutexStack[i], 0, 1);  // inicializa
        }

    	pthread_t *threads = (pthread_t*) malloc(sizeof(pthread_t) * quantThreads);
        int mythread[quantThreads];

        root.solve(0.0, 100.0, -1);

	    for (int i = 0; i < quantThreads; i++){
            mythread[i] = i;
	    	pthread_create(&threads[i], NULL, run, &mythread[i]);
	    }

	    for (int i = 0; i < quantThreads; i++){
	    	pthread_join(threads[i], NULL);
	    }

	    printf("modo: paralelo com %d threads\n", quantThreads);
    }else{
    	root.solveRec(0.0, 100.0, -1);
    	printf("\nmodo: sequencial\n\n");
    }

    printf("saiu\n");

    fprintf(stderr, "Optimal value = %g.\n", upperBound);
    return 0;   
}

void *run(void *args){

	Stopwatch stopWatch;
	START_STOPWATCH(stopWatch);

    int id = *(int*) args;
    /*BBNode *param = nodeVetor[id].child;
    do {
        again: param->solve(0.0, 100.0, id);
        sem_wait(&mutexStack[id]);
        param = pop(&load[id]);
        sem_post(&mutexStack[id]);
    } while(load[id] != NULL);*/

    sem_wait(&mutexStack[id]);
    BBNode *param = pop(&load[id]);
    sem_post(&mutexStack[id]);
    while(param != NULL) {
        again: param->solve(0.0, 100.0, id);
        sem_wait(&mutexStack[id]);
        param = pop(&load[id]);
        sem_post(&mutexStack[id]);
    }

    for (int i = 0; i < quantThreads; i++){
        if (i == id) continue;
        sem_wait(&mutexStack[i]);
        
        if (!isEmpty(load[i])){
            param = pop(&load[i]);
            sem_post(&mutexStack[i]);
            goto again; 
        }
        sem_post(&mutexStack[i]);
    }

    STOP_STOPWATCH(stopWatch);
    printf("thread %d - %.4lf\n", id, stopWatch.mElapsedTime);
}

Stack *startStack(){
    return NULL;
}

Stack *push(Stack *stack, BBNode *value){
    Stack *newNode = (Stack*) malloc(sizeof(Stack));
    newNode->value = value;
    newNode->next = stack;
    return newNode;
}

BBNode *pop(Stack **stack){
    if ((*stack) != NULL){
        BBNode *node = (*stack)->value;
        *stack = (*stack)->next;
        return node;
    }
    return NULL;
}

bool isEmpty(Stack *stack){
    if (stack == NULL)
        return true;
    else
        return false;
}