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
	// save variable's neighbor to the cache.
	for (Variable* v : allVars){
		neighborCache[v] = network.getNeighborsOfVariable(v);
	}
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
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

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<unordered_map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
	unordered_map<Variable*,Domain> modifiedVariables;
	// Optimization :  no need to check assigned value twice or more.
	// eg: editing Cell(1,1) will trigger three constraints, we remove all values assigned on Cell(1,1)
	// out of domain of Cell(1,1)'s neighbor at the first iteration.
	unordered_set<Variable*> processedAssignments;
	// Optimization: incremental propagation with queue
	// Process variables that need propagation( initially from modified constraints)
	// then automatically added when singleton is detected, we assign value to these singleton
	queue<Variable*> propagationQueue;
	unordered_set<Variable*> inQueue;

	vector<Constraint*> RMC = network.getModifiedConstraints();

	for (int i = 0; i < RMC.size(); ++i){
		//  vector of values in that constraint(row/col/cell). 
		vector<Variable*> LV = RMC[i]->vars;

		for (int j = 0; j < LV.size(); ++j){
			if (LV[j]->isAssigned() && processedAssignments.find(LV[j]) == processedAssignments.end()){
				// marked value as checked
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
			// search neighbors using cache
			vector<Variable*>& Neighbors = neighborCache[assignedVar];

			for (int k = 0; k < Neighbors.size(); ++k){
				// Only process unassigned neighbors
				if (!Neighbors[k]->isAssigned()){
					const Domain& D = Neighbors[k]->getDomain();
						
					// If neighbor's domain contains the assigned value,
					// remove it from its domain. 
					if (D.contains(assignedValue)){
						// Optimization: Check if the domain will be empty,early return
						if (D.size() == 1)
							return make_pair(modifiedVariables,false);

						// push to trail for future backtracking prupose
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

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */
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
            // ============================================
            // 2a: Hidden Singles
            // ============================================
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
 
            // ============================================
            // 2b: Hidden Pairs
            // ============================================
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
 
            // ============================================
            // 2c: Naked Pairs
            // ============================================
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
    return make_pair(assignedVariables, network.isConsistent());
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
    int boardSize = sudokuGrid.get_p() * sudokuGrid.get_q();
    // --- Step 1: Forward Checking with cascade ---
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
                        return false;
 
                    trail->push(neighbor);
                    neighbor->removeValueFromDomain(assignedValue);
 
                    if (neighbor->getDomain().size() == 0)
                        return false;
 
                    if (neighbor->getDomain().size() == 1)
                    {
                        int onlyValue = neighbor->getDomain().getValues()[0];
                        bool canAssign = true;
                        for (Variable* nn : neighborCache[neighbor])
                        {
                            if (nn->isAssigned() && nn->getAssignment() == onlyValue)
                            { canAssign = false; break; }
                        }
                        if (!canAssign) return false;
 
                        trail->push(neighbor);
                        neighbor->assignValue(onlyValue);
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
 
    // --- Step 2: Hidden Singles + Naked Pairs (+ advanced for large boards) ---
    const vector<Constraint>& allConstraints = network.getConstraints();
    bool changed = true;
    while (changed)
    {
        changed = false;
 
        for (const Constraint& c : allConstraints)
        {
            // Collect unassigned vars and assigned values
            vector<Variable*> unassigned;
            unordered_set<int> assignedVals;
            for (Variable* v : c.vars)
            {
                if (v->isAssigned())
                    assignedVals.insert(v->getAssignment());
                else
                    unassigned.push_back(v);
            }
 
            if (unassigned.empty()) continue;
 
            // ============================================
            // 2a: Hidden Singles
            // ============================================
            unordered_map<int, vector<Variable*>> valueToCandidates;
            for (Variable* v : unassigned)
            {
                const vector<int>& vals = v->getDomain().getValues();
                for (int val : vals)
                    valueToCandidates[val].push_back(v);
            }
 
            for (auto& entry : valueToCandidates)
            {
                int val = entry.first;
                vector<Variable*>& candidates = entry.second;
 
                if (assignedVals.count(val)) continue;
 
                if (candidates.size() == 0)
                    return false;
 
                if (candidates.size() == 1)
                {
                    Variable* target = candidates[0];
                    if (!target->isAssigned())
                    {
                        bool canAssign = true;
                        for (Variable* nn : neighborCache[target])
                        {
                            if (nn->isAssigned() && nn->getAssignment() == val)
                            { canAssign = false; break; }
                        }
                        if (!canAssign) return false;
 
                        trail->push(target);
                        target->assignValue(val);
                        changed = true;
 
                        for (Variable* neighbor : neighborCache[target])
                        {
                            if (!neighbor->isAssigned())
                            {
                                const Domain& D = neighbor->getDomain();
                                if (D.contains(val))
                                {
                                    if (D.size() == 1) return false;
                                    trail->push(neighbor);
                                    neighbor->removeValueFromDomain(val);
                                    if (neighbor->getDomain().size() == 0) return false;
 
                                    if (neighbor->getDomain().size() == 1)
                                    {
                                        int ov = neighbor->getDomain().getValues()[0];
                                        bool ok = true;
                                        for (Variable* nn2 : neighborCache[neighbor])
                                        {
                                            if (nn2->isAssigned() && nn2->getAssignment() == ov)
                                            { ok = false; break; }
                                        }
                                        if (!ok) return false;
                                        trail->push(neighbor);
                                        neighbor->assignValue(ov);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
 
            // ============================================
            // 2b: Naked Pairs
            // ============================================
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
                            if (v == pairCandidates[i] || v == pairCandidates[j]) continue;
                            if (v->isAssigned()) continue;
 
                            const Domain& D = v->getDomain();
                            bool hasVal1 = D.contains(val1);
                            bool hasVal2 = D.contains(val2);
 
                            if (!hasVal1 && !hasVal2) continue;
 
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
 
                            if (v->getDomain().size() == 0) return false;
 
                            if (v->getDomain().size() == 1 && !v->isAssigned())
                            {
                                int ov = v->getDomain().getValues()[0];
                                bool ok = true;
                                for (Variable* nn : neighborCache[v])
                                {
                                    if (nn->isAssigned() && nn->getAssignment() == ov)
                                    { ok = false; break; }
                                }
                                if (!ok) return false;
                                trail->push(v);
                                v->assignValue(ov);
                                changed = true;
                            }
                        }
                    }
                }
            }
 
            // ============================================
            // 2c: Hidden Pairs + Naked Triples (large boards only)
            // ============================================
            if (boardSize > 9)
            {
                // --- Hidden Pairs ---
                unordered_map<int, vector<Variable*>> vtc2;
                for (Variable* v : c.vars)
                {
                    if (!v->isAssigned())
                    {
                        const vector<int>& vals = v->getDomain().getValues();
                        for (int val : vals)
                            vtc2[val].push_back(v);
                    }
                }
 
                vector<int> twoPlaceValues;
                for (auto& entry : vtc2)
                {
                    if (entry.second.size() == 2)
                        twoPlaceValues.push_back(entry.first);
                }
 
                for (int i = 0; i < (int)twoPlaceValues.size(); i++)
                {
                    for (int j = i + 1; j < (int)twoPlaceValues.size(); j++)
                    {
                        int v1 = twoPlaceValues[i];
                        int v2 = twoPlaceValues[j];
 
                        vector<Variable*>& cells1 = vtc2[v1];
                        vector<Variable*>& cells2 = vtc2[v2];
 
                        if (cells1.size() == 2 && cells2.size() == 2 &&
                            ((cells1[0] == cells2[0] && cells1[1] == cells2[1]) ||
                             (cells1[0] == cells2[1] && cells1[1] == cells2[0])))
                        {
                            Variable* cellA = cells1[0];
                            Variable* cellB = cells1[1];
 
                            for (Variable* cell : {cellA, cellB})
                            {
                                if (cell->isAssigned()) continue;
 
                                const vector<int>& domVals = cell->getDomain().getValues();
                                bool pushed = false;
 
                                for (int dv : domVals)
                                {
                                    if (dv != v1 && dv != v2)
                                    {
                                        if (!pushed)
                                        {
                                            trail->push(cell);
                                            pushed = true;
                                        }
                                        cell->removeValueFromDomain(dv);
                                        changed = true;
                                    }
                                }
 
                                if (cell->getDomain().size() == 0)
                                    return false;
 
                                if (cell->getDomain().size() == 1 && !cell->isAssigned())
                                {
                                    int ov = cell->getDomain().getValues()[0];
                                    bool ok = true;
                                    for (Variable* nn : neighborCache[cell])
                                    {
                                        if (nn->isAssigned() && nn->getAssignment() == ov)
                                        { ok = false; break; }
                                    }
                                    if (!ok) return false;
                                    trail->push(cell);
                                    cell->assignValue(ov);
                                    changed = true;
                                }
                            }
                        }
                    }
                }
 
                // --- Naked Triples ---
                vector<Variable*> triCandidates;
                for (Variable* v : c.vars)
                {
                    if (!v->isAssigned())
                    {
                        int ds = v->getDomain().size();
                        if (ds == 2 || ds == 3)
                            triCandidates.push_back(v);
                    }
                }
 
                for (int i = 0; i < (int)triCandidates.size(); i++)
                {
                    for (int j = i + 1; j < (int)triCandidates.size(); j++)
                    {
                        for (int k = j + 1; k < (int)triCandidates.size(); k++)
                        {
                            unordered_set<int> unionDomain;
                            for (int val : triCandidates[i]->getDomain().getValues())
                                unionDomain.insert(val);
                            for (int val : triCandidates[j]->getDomain().getValues())
                                unionDomain.insert(val);
                            for (int val : triCandidates[k]->getDomain().getValues())
                                unionDomain.insert(val);
 
                            if (unionDomain.size() == 3)
                            {
                                for (Variable* v : c.vars)
                                {
                                    if (v == triCandidates[i] || v == triCandidates[j] || v == triCandidates[k])
                                        continue;
                                    if (v->isAssigned()) continue;
 
                                    const Domain& D = v->getDomain();
                                    bool pushed = false;
 
                                    for (int uv : unionDomain)
                                    {
                                        if (D.contains(uv))
                                        {
                                            if (!pushed)
                                            {
                                                trail->push(v);
                                                pushed = true;
                                            }
                                            v->removeValueFromDomain(uv);
                                            changed = true;
                                        }
                                    }
 
                                    if (v->getDomain().size() == 0) return false;
 
                                    if (v->getDomain().size() == 1 && !v->isAssigned())
                                    {
                                        int ov = v->getDomain().getValues()[0];
                                        bool ok = true;
                                        for (Variable* nn : neighborCache[v])
                                        {
                                            if (nn->isAssigned() && nn->getAssignment() == ov)
                                            { ok = false; break; }
                                        }
                                        if (!ok) return false;
                                        trail->push(v);
                                        v->assignValue(ov);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            } // end if boardSize > 9
 
        } // end for each constraint
    } // end while changed
 
    return network.isConsistent();
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
    Variable* best = nullptr;
    int smallestDomainSize = INT_MAX;
    int bestDegree = -1;

    for (Variable* v : network.getVariables())
    {
        if (!v->isAssigned())
        {
            int domainSize = v->getDomain().size();
            int degree = 0;
            for (Variable* n : neighborCache[v])
                if (!n->isAssigned()) degree++;

            if (domainSize < smallestDomainSize ||
                (domainSize == smallestDomainSize && degree > bestDegree))
            {
                smallestDomainSize = domainSize;
                bestDegree = degree;
                best = v;
            }
        }
    }

    return best;
}



/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
	vector<Variable*> result;
	int smallestDomainSize = INT_MAX;
	int mostConstraints = -1;

	for (Variable* v: network.getVariables())
	{
		if (!v->isAssigned()){
			int domainSize = v->getDomain().size();
			// found a smaller domain, reset the constraint
			if (domainSize < smallestDomainSize){
				smallestDomainSize = domainSize;
				mostConstraints = -1;
				result.clear();
			}
			// only node with smaller domain could enter here
			if (domainSize == smallestDomainSize){
				int degree = 0;
				for (Variable* neighbor: neighborCache[v]){
					if (!neighbor->isAssigned())
						degree++;
				}
			// found 
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

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
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
 
        // Quick skip: can't be better than current best on primary criterion
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
        {
            isBetter = true;
        }
        else if (domainSize == bestDomainSize)
        {
            // Tie-break 1: smaller MAD (more constrained neighborhood)
            if (madScore < bestMAD)
            {
                isBetter = true;
            }
            else if (madScore == bestMAD)
            {
                // Tie-break 2: higher degree (more unassigned neighbors)
                if (degree > bestDegree)
                {
                    isBetter = true;
                }
            }
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

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */
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

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
 
    // Fast path: if only one value, no sorting needed
    if (values.size() <= 1)
        return values;
 
    vector<Variable*>& neighbors = neighborCache[v];
 
    vector<pair<int, int>> valueScores; // (score, value)
    valueScores.reserve(values.size());
 
    for (int val : values)
    {
        int score = 0;
        bool causesWipeout = false;
 
        for (Variable* neighbor : neighbors)
        {
            if (neighbor->isAssigned()) continue;
 
            const Domain& D = neighbor->getDomain();
            if (D.contains(val))
            {
                score++;
 
                // Wipeout: this would empty a neighbor's domain
                if (D.size() == 1)
                {
                    causesWipeout = true;
                    break;
                }
 
                // Lookahead: if removing val leaves neighbor with 1 value,
                // check if that remaining value conflicts with ITS neighbors
                if (D.size() == 2)
                {
                    const vector<int>& nVals = D.getValues();
                    int otherVal = (nVals[0] == val) ? nVals[1] : nVals[0];
 
                    for (Variable* nn : neighborCache[neighbor])
                    {
                        if (nn != v && nn->isAssigned() && nn->getAssignment() == otherVal)
                        {
                            score += 100; // heavy penalty: forced conflict
                            break;
                        }
                    }
                }
            }
        }
 
        if (causesWipeout)
            valueScores.push_back(make_pair(10000, val));
        else
            valueScores.push_back(make_pair(score, val));
    }
 
    sort(valueScores.begin(), valueScores.end());
 
    vector<int> result;
    result.reserve(valueScores.size());
    for (auto& p : valueScores)
        result.push_back(p.second);
    return result;
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

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
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
