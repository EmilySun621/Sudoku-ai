#include"BTSolver.hpp"
#include <algorithm>     
#include <unordered_map> 
#include <unordered_set> 
#include <queue> 
#include <climits>        
using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh; 
	cChecks =  cc;

	trail = _trail;
	buildNeighborCache();
}

void BTSolver::buildNeighborCache()
{
	unordered_set<Variable*> allVars;
	for (Constraint& c: network.getConstraints()){
		for (Variable* v: c.vars){
			allVars.insert(v);
		}
	}
	for (Variable* v : allVars){
		neighborCache[v] = network.getNeighborsOfVariable(v);
	}
}

// =====================================================================
// Consistency Checks
// =====================================================================

bool BTSolver::assignmentsCheck ( void )
{
	for (Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;
	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*>& Neighbors = neighborCache[LV[j]];
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            const Domain& D = toAssign[i]->getDomain();
            const vector<int>& assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

pair<unordered_map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
	unordered_map<Variable*,Domain> modifiedVariables;
	unordered_set<Variable*> processedAssignments;
	queue<Variable*> propagationQueue;
	unordered_set<Variable*> inQueue;

	vector<Constraint*> RMC = network.getModifiedConstraints();

	for (int i = 0; i < RMC.size(); ++i){
		vector<Variable*> LV = RMC[i]->vars;
		for (int j = 0; j < LV.size(); ++j){
			if (LV[j]->isAssigned() && processedAssignments.find(LV[j]) == processedAssignments.end()){
				processedAssignments.insert(LV[j]);
				if (inQueue.find(LV[j]) == inQueue.end()){
					propagationQueue.push(LV[j]);
					inQueue.insert(LV[j]);
				}
			}
		}
	}
	while (!propagationQueue.empty()){
			Variable* assignedVar = propagationQueue.front();
			propagationQueue.pop();
			inQueue.erase(assignedVar);

			if (!assignedVar->isAssigned()) continue;

			int assignedValue = assignedVar->getAssignment();
			vector<Variable*>& Neighbors = neighborCache[assignedVar];

			for (int k = 0; k < Neighbors.size(); ++k){
				if (!Neighbors[k]->isAssigned()){
					const Domain& D = Neighbors[k]->getDomain();
					if (D.contains(assignedValue)){
						if (D.size() == 1)
							return make_pair(modifiedVariables,false);

						trail->push(Neighbors[k]);
						Neighbors[k]->removeValueFromDomain(assignedValue);

						Domain updatedDomain = Neighbors[k]->getDomain();
						modifiedVariables[Neighbors[k]] = updatedDomain;
						
						if (updatedDomain.size() == 0){
							return make_pair(modifiedVariables,false);
						}
						if (updatedDomain.size() == 1 && 
					    	!Neighbors[k]->isAssigned() && 
					    	Neighbors[k]->getDomain().size() == 1) { 
						
							int onlyValue = updatedDomain.getValues()[0];
						
							bool canAssign = true;
							vector<Variable*>& neighborsOfNeighbor = neighborCache[Neighbors[k]];
							for (Variable* nn : neighborsOfNeighbor) {
								if (nn->isAssigned() && nn->getAssignment() == onlyValue) {
									canAssign = false;
									break;
								}
							}
						
							if (!canAssign) {
								return make_pair(modifiedVariables, false);
							}

							trail->push(Neighbors[k]);
							Neighbors[k]->assignValue(onlyValue);

							if (inQueue.find(Neighbors[k]) == inQueue.end()){
								propagationQueue.push(Neighbors[k]);
								inQueue.insert(Neighbors[k]);
							}
						}
					}
				}
			}
		}
	return make_pair(modifiedVariables,true);
}

pair<unordered_map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
    unordered_map<Variable*, int> assignedVariables;

    // ---- Part 1: Forward Checking ----
    queue<Variable*> propagationQueue;
    unordered_set<Variable*> inQueue;
    unordered_set<Variable*> processed;

    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (Constraint* c : RMC)
    {
        for (Variable* v : c->vars)
        {
            if (v->isAssigned() && processed.find(v) == processed.end())
            {
                processed.insert(v);
                if (inQueue.find(v) == inQueue.end())
                {
                    propagationQueue.push(v);
                    inQueue.insert(v);
                }
            }
        }
    }

    while (!propagationQueue.empty())
    {
        Variable* assignedVar = propagationQueue.front();
        propagationQueue.pop();
        inQueue.erase(assignedVar);

        if (!assignedVar->isAssigned()) continue;

        int assignedValue = assignedVar->getAssignment();
        vector<Variable*>& neighbors = neighborCache[assignedVar];

        for (Variable* neighbor : neighbors)
        {
            if (!neighbor->isAssigned())
            {
                const Domain& D = neighbor->getDomain();
                if (D.contains(assignedValue))
                {
                    if (D.size() == 1)
                        return make_pair(assignedVariables, false);

                    trail->push(neighbor);
                    neighbor->removeValueFromDomain(assignedValue);

                    if (neighbor->getDomain().size() == 0)
                        return make_pair(assignedVariables, false);

                    if (neighbor->getDomain().size() == 1)
                    {
                        int onlyValue = neighbor->getDomain().getValues()[0];

                        bool canAssign = true;
                        vector<Variable*>& neighborsOfNeighbor = neighborCache[neighbor];
                        for (Variable* nn : neighborsOfNeighbor)
                        {
                            if (nn->isAssigned() && nn->getAssignment() == onlyValue)
                            {
                                canAssign = false;
                                break;
                            }
                        }

                        if (!canAssign)
                            return make_pair(assignedVariables, false);

                        trail->push(neighbor);
                        neighbor->assignValue(onlyValue);
                        assignedVariables[neighbor] = onlyValue;

                        if (inQueue.find(neighbor) == inQueue.end())
                        {
                            propagationQueue.push(neighbor);
                            inQueue.insert(neighbor);
                        }
                    }
                }
            }
        }
    }

    // ---- Part 2: Hidden Singles + Hidden Pairs + Naked Pairs ----
    const vector<Constraint>& allConstraints = network.getConstraints();
    bool changed = true;
    while (changed)
    {
        changed = false;
        for (const Constraint& c : allConstraints)
        {
            // 2a: Hidden Singles
            unordered_map<int, vector<Variable*>> valueToCandidates;
            unordered_set<int> assignedVals;

            for (Variable* v : c.vars)
            {
                if (v->isAssigned())
                    assignedVals.insert(v->getAssignment());
                else
                {
                    const vector<int>& vals = v->getDomain().getValues();
                    for (int val : vals)
                        valueToCandidates[val].push_back(v);
                }
            }

            for (auto& entry : valueToCandidates)
            {
                int val = entry.first;
                vector<Variable*>& candidates = entry.second;

                if (assignedVals.count(val))
                    continue;

                if (candidates.size() == 0)
                    return make_pair(assignedVariables, false);

                if (candidates.size() == 1)
                {
                    Variable* target = candidates[0];
                    if (!target->isAssigned())
                    {
                        bool canAssign = true;
                        vector<Variable*>& neighborsOfTarget = neighborCache[target];
                        for (Variable* nn : neighborsOfTarget)
                        {
                            if (nn->isAssigned() && nn->getAssignment() == val)
                            {
                                canAssign = false;
                                break;
                            }
                        }

                        if (!canAssign)
                            return make_pair(assignedVariables, false);

                        trail->push(target);
                        target->assignValue(val);
                        assignedVariables[target] = val;
                        changed = true;

                        vector<Variable*>& neighbors = neighborCache[target];
                        for (Variable* neighbor : neighbors)
                        {
                            if (!neighbor->isAssigned())
                            {
                                const Domain& D = neighbor->getDomain();
                                if (D.contains(val))
                                {
                                    if (D.size() == 1)
                                        return make_pair(assignedVariables, false);

                                    trail->push(neighbor);
                                    neighbor->removeValueFromDomain(val);

                                    if (neighbor->getDomain().size() == 0)
                                        return make_pair(assignedVariables, false);

                                    if (neighbor->getDomain().size() == 1)
                                    {
                                        int onlyVal = neighbor->getDomain().getValues()[0];
                                        bool ok = true;
                                        for (Variable* nn2 : neighborCache[neighbor])
                                        {
                                            if (nn2->isAssigned() && nn2->getAssignment() == onlyVal)
                                            {
                                                ok = false;
                                                break;
                                            }
                                        }
                                        if (!ok)
                                            return make_pair(assignedVariables, false);

                                        trail->push(neighbor);
                                        neighbor->assignValue(onlyVal);
                                        assignedVariables[neighbor] = onlyVal;
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // 2b: Hidden Pairs
            unordered_map<int, vector<Variable*>> vtc;
            for (Variable* v : c.vars)
            {
                if (!v->isAssigned())
                {
                    const vector<int>& vals = v->getDomain().getValues();
                    for (int val : vals)
                        vtc[val].push_back(v);
                }
            }

            vector<int> twoPlaceVals;
            for (auto& e : vtc)
                if (!assignedVals.count(e.first) && e.second.size() == 2)
                    twoPlaceVals.push_back(e.first);

            for (size_t i = 0; i < twoPlaceVals.size(); i++)
            {
                for (size_t j = i + 1; j < twoPlaceVals.size(); j++)
                {
                    int v1 = twoPlaceVals[i], v2 = twoPlaceVals[j];
                    vector<Variable*>& c1 = vtc[v1];
                    vector<Variable*>& c2 = vtc[v2];
                    if (c1.size() != 2 || c2.size() != 2) continue;
                    bool sameCells = (c1[0] == c2[0] && c1[1] == c2[1]) ||
                                     (c1[0] == c2[1] && c1[1] == c2[0]);
                    if (!sameCells) continue;

                    Variable* A = c1[0];
                    Variable* B = c1[1];
                    for (Variable* cell : {A, B})
                    {
                        if (cell->isAssigned()) continue;
                        const vector<int>& dom = cell->getDomain().getValues();
                        bool pushed = false;
                        for (int dv : dom)
                        {
                            if (dv != v1 && dv != v2)
                            {
                                if (!pushed) { trail->push(cell); pushed = true; }
                                cell->removeValueFromDomain(dv);
                                changed = true;
                            }
                        }
                        if (cell->getDomain().size() == 0)
                            return make_pair(assignedVariables, false);
                        if (cell->getDomain().size() == 1 && !cell->isAssigned())
                        {
                            int ov = cell->getDomain().getValues()[0];
                            bool ok = true;
                            for (Variable* nn : neighborCache[cell])
                                if (nn->isAssigned() && nn->getAssignment() == ov)
                                { ok = false; break; }
                            if (!ok) return make_pair(assignedVariables, false);
                            trail->push(cell);
                            cell->assignValue(ov);
                            assignedVariables[cell] = ov;
                            changed = true;
                        }
                    }
                }
            }

            // 2c: Naked Pairs
            vector<Variable*> pairCandidates;
            for (Variable* v : c.vars)
            {
                if (!v->isAssigned() && v->getDomain().size() == 2)
                    pairCandidates.push_back(v);
            }

            for (int i = 0; i < (int)pairCandidates.size(); i++)
            {
                for (int j = i + 1; j < (int)pairCandidates.size(); j++)
                {
                    const vector<int>& d1 = pairCandidates[i]->getDomain().getValues();
                    const vector<int>& d2 = pairCandidates[j]->getDomain().getValues();

                    if (d1.size() == 2 && d2.size() == 2 &&
                        ((d1[0] == d2[0] && d1[1] == d2[1]) ||
                         (d1[0] == d2[1] && d1[1] == d2[0])))
                    {
                        int val1 = d1[0];
                        int val2 = d1[1];

                        for (Variable* v : c.vars)
                        {
                            if (v == pairCandidates[i] || v == pairCandidates[j])
                                continue;
                            if (v->isAssigned())
                                continue;

                            const Domain& D = v->getDomain();
                            bool hasVal1 = D.contains(val1);
                            bool hasVal2 = D.contains(val2);

                            if (!hasVal1 && !hasVal2)
                                continue;

                            trail->push(v);

                            if (hasVal1)
                            {
                                v->removeValueFromDomain(val1);
                                changed = true;
                            }
                            if (hasVal2)
                            {
                                v->removeValueFromDomain(val2);
                                changed = true;
                            }

                            if (v->getDomain().size() == 0)
                                return make_pair(assignedVariables, false);

                            if (v->getDomain().size() == 1 && !v->isAssigned())
                            {
                                int onlyVal = v->getDomain().getValues()[0];
                                bool ok = true;
                                for (Variable* nn : neighborCache[v])
                                {
                                    if (nn->isAssigned() && nn->getAssignment() == onlyVal)
                                    {
                                        ok = false;
                                        break;
                                    }
                                }
                                if (!ok)
                                    return make_pair(assignedVariables, false);

                                trail->push(v);
                                v->assignValue(onlyVal);
                                assignedVariables[v] = onlyVal;
                                changed = true;

                                for (Variable* neighbor : neighborCache[v])
                                {
                                    if (!neighbor->isAssigned())
                                    {
                                        const Domain& ND = neighbor->getDomain();
                                        if (ND.contains(onlyVal))
                                        {
                                            if (ND.size() == 1)
                                                return make_pair(assignedVariables, false);
                                            trail->push(neighbor);
                                            neighbor->removeValueFromDomain(onlyVal);
                                            if (neighbor->getDomain().size() == 0)
                                                return make_pair(assignedVariables, false);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    // Propagation guarantees consistency — skip expensive network.isConsistent()
    return make_pair(assignedVariables, true);
}



bool BTSolver::getTournCC ( void )
{
   return norvigCheck().second;
}




// =====================================================================
// Variable Selectors
// =====================================================================

Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;
	return nullptr;
}

Variable* BTSolver::getMRV ( void )
{
    Variable* best = nullptr;
    int smallestDomainSize = INT_MAX;

    for (Variable* v : network.getVariables())
    {
        if (!v->isAssigned())
        {
            int domainSize = v->getDomain().size();
            if (domainSize < smallestDomainSize)
            {
                smallestDomainSize = domainSize;
                best = v;
            }
        }
    }
    return best;
}

vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
	vector<Variable*> result;
	int smallestDomainSize = INT_MAX;
	int mostConstraints = -1;

	for (Variable* v: network.getVariables())
	{
		if (!v->isAssigned()){
			int domainSize = v->getDomain().size();
			if (domainSize < smallestDomainSize){
				smallestDomainSize = domainSize;
				mostConstraints = -1;
				result.clear();
			}
			if (domainSize == smallestDomainSize){
				int degree = 0;
				for (Variable* neighbor: neighborCache[v]){
					if (!neighbor->isAssigned())
						degree++;
				}
			if (degree > mostConstraints){
				mostConstraints = degree;
				result.clear();
				result.push_back(v);
			}
			else if (degree == mostConstraints){
				result.push_back(v);
			}
		  }
		}
	}
    return result;
}

Variable* BTSolver::getTournVar ( void )
{
    Variable* best = nullptr;
    int bestDomainSize = INT_MAX;
    int bestMAD = INT_MAX;
    int bestDegree = -1;

    for (Variable* v : network.getVariables())
    {
        if (v->isAssigned()) continue;

        int domainSize = v->getDomain().size();
        if (domainSize > bestDomainSize) continue;

        int madScore = 0;
        int degree = 0;
        for (Variable* neighbor : neighborCache[v])
        {
            if (!neighbor->isAssigned())
            {
                madScore += neighbor->getDomain().size();
                degree++;
            }
        }

        bool isBetter = false;
        if (domainSize < bestDomainSize)
            isBetter = true;
        else if (domainSize == bestDomainSize)
        {
            if (madScore < bestMAD)
                isBetter = true;
            else if (madScore == bestMAD && degree > bestDegree)
                isBetter = true;
        }

        if (isBetter)
        {
            best = v;
            bestDomainSize = domainSize;
            bestMAD = madScore;
            bestDegree = degree;
        }
    }
    return best;
}
// =====================================================================
// Value Selectors
// =====================================================================

vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
    vector<int> values = v->getDomain().getValues();
    vector<Variable*>& neighbors = neighborCache[v];

    unordered_map<int, int> elimCount;
    for (int val : values)
        for (Variable* neighbor : neighbors)
            if (!neighbor->isAssigned() && neighbor->getDomain().contains(val))
                elimCount[val]++;

    sort(values.begin(), values.end(), [&](int a, int b) {
        int ea = elimCount[a];
        int eb = elimCount[b];
        return ea < eb || (ea == eb && a < b);
    });

    return values;
}

vector<int> BTSolver::getTournVal ( Variable* v )
{
    // With zero backtracks, value ordering doesn't matter — return directly
    return v->getDomain().getValues();
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}
		hasSolution = true;
		return 0;
	}

	for ( int i : getNextValues( v ) )
	{
		trail->placeTrailMarker();
		trail->push( v );
		v->assignValue( i );

		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
		}

		if ( hasSolution )
			return 0;

		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
	{
		vector<Variable*> cands = MRVwithTieBreaker();
		return cands.empty() ? nullptr : cands[0];
	}

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}