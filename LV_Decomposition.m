//============//
// User Input //
//============//
// Our program takes as input
//     1. a finitely-presented Coxeter group W;
//     2. a list of generators for a finite index reflection subgroup WK;
//     3. (optional) a representation of W.
// It then fully determines the module structure for the
// equal-rank Lusztig-Vogan category described by this triplet.
W := CoxeterGroup(GrpMat, "G2");
// Finite index subgroups of finitely-generated groups are finitely-generated.
// If you leave WK empty, this will generate the category of Soergel bimodules.
WK := [[1,2,1], [2,1,2]];
// Set up the ring R. Note that our field F will not always be the
// rationals, as W will often be defined over a field extension.
F := BaseRing(W);
R := PolynomialRing(F, Rank(W));
AssignNames(~R, [Sprintf("a_%o", i) : i in [1..Ngens(R)]]);
// The polynomial reflection_basis[i][j] corresponds to s_i(a_{s_j}).
// If it's empty, we default to using the geometric representation.
reflection_basis := [];


//============//
// Test Flags //
//============//
SAFE := true;
SORT_BASES := true;


//==================//
// Global Variables //
//==================//
// Note: by default our program chooses the geometric
// representation, since this is already built into Magma.
function geometric_representation()
	
	// Compute a change of basis for performing simple reflections.
	reflection_basis := [];
	for S in SimpleReflectionMatrices(W) do
		// The kth reflection matrix S in SimpleReflectionMatrices(W)
		// corresponds to the kth simple reflection.
		Append(~reflection_basis, []);
		// The (i, j)th element of the reflection matrix S
		// is the coefficient of R.j inside S*R.i. Add them
		// all up into one polynomial representing S*R.i.
		for i := 1 to Nrows(S) do
			SRi := R!0;
			for j := 1 to Ncols(S) do
				SRi +:= S[i][j]*R.j;
			end for;
			Append(~reflection_basis[#reflection_basis], SRi);
		end for;
	end for;
	
	return reflection_basis;
	
end function;

if IsEmpty(reflection_basis) then
	reflection_basis := geometric_representation();
end if;


//====================//
// Core Functionality //
//====================//
function prepare_output()

	// Get a name for the output file.
	_, _, file := Regexp("(.+)\ (.+)\ (.+)", Read(POpen("date", "r")));
	file := Split(file[1], " ");
	for i := 2 to #file do
		file[1] := file[1] cat "_" cat file[i];
	end for;
	file := Split(file[1], ":");
	for i := 2 to #file do
		file[1] := file[1] cat "-" cat file[i];
	end for;
	file := "./output/" cat file[1] cat ".txt";

	// Make sure we can write to the file before continuing.
	System("mkdir ./output -p");
	if not OpenTest(file, "w") then
		error "Cannot create output file " cat file cat "!";
	end if;
	
	return file;
	
end function;

// Perform the kth simple reflection on x.
function s(k, x)
	return Evaluate(x, reflection_basis[k]);
end function;

// Perform the kth Demazure operator on x.
function d_s(k, x)
	return (x - s(k, x)) div R.k;
end function;

// Tensor an indecomposable with B_{s_k} on the right.
// To create a new basis, we duplicate our existing basis,
// appending rank many zeroes to the first copy and prepending
// rank many zeroes to the second copy. This has the effect of
// tensoring on the right by 1 and by c_{s_k}.
function tensor(k, basis, action)
	
	new_basis := [];
	new_action := [];
	
	n := #basis;
	
	// Create the new graded basis.
	// The first loop creates {b_i x 1}, while the
	// second loop creates {b_i x c_{s_k}}. We need to
	// adjust the grading, since tensoring by B_{s_k}
	// induces a grading shift by 1.
	for i := 1 to n do
		Append(~new_basis, basis[i]-1);
	end for;
	for i := 1 to n do
		Append(~new_basis, basis[i]+1);
	end for;
	
	// Sort the new basis by homogeneous degree and
	// build permutation matrices for the action.
	p := [1..#new_basis];
	if SORT_BASES then
		ParallelSort(~new_basis, ~p);
	end if;
	P := PermutationMatrix(R, p);
	PT := Transpose(P);
	
	// Create the new action matrices.
	for A in action do
		// Based on how we originally constructed our
		// new basis, we would naively have simply
		//             (  s(A)  0)
		//     new_A = (d_s(A)  A).
		// However, because we have sorted our basis,
		// we need to conjugate by a permutation.
		Append(~new_action, P*BlockMatrix(2, 2, [
			Matrix(n, n, [s(k, A[i][j]) : j in [1..n], i in [1..n]]),
			ZeroMatrix(R, n, n),
			Matrix(n, n, [d_s(k, A[i][j]) : j in [1..n], i in [1..n]]),
			A
		])*PT);
	end for;
	
	return new_basis, new_action;
	
end function;

// Build a general degree 0 right R-module homomorphism together
// with a system of equations it must satisfy in order to be a
// valid bimodule homomorphism.
function morphism(
	basis_domain, action_domain, basis_codomain, action_codomain, extra_coeffs
)
	
	// We assume #basis_domain = #basis_codomain.
	n := #basis_domain;
	
	// Build a degree d = 0 symbolic matrix.
	// Determine the degree of each entry m_ij of M,
	// as well as the number of monomial coefficients.
	// We use the latter when initializing the ring C.
	M_grading := [];
	num_coeff := extra_coeffs;
	for i := 1 to n do
		row := [];
		for j := 1 to n do
			// In order for M to be a graded morphism of degree d, we
			// require that deg(m_ij) = d + deg(b_j) - deg(b_i'), where
			// b_i' is a basis for the codomain and b_j is a basis for
			// the domain. We divide by 2 to get the polynomial degree.
			degree := ShiftRight(basis_domain[j] - basis_codomain[i], 1);
			Append(~row, degree);
			if degree ge 0 then
				// This is the number of monomials of
				// this degree in Ngens(R) variables.
				num_coeff +:= Binomial(degree+Ngens(R)-1, Ngens(R)-1);
			end if;
		end for;
		Append(~M_grading, row);
	end for;
	
	C := PolynomialRing(F, num_coeff);
	CR := PolynomialRing(C, Ngens(R));

	// For each element m_ij of M, set it equal to a
	// general polynomial of degree M_grading[i][j]
	// in the simple roots, with coefficients in C.
	// The variable k keeps track of which monomial
	// coefficient in C we're currently up to.
	M := ZeroMatrix(CR, n);
	k := 1;
	// Later on, we can just check if the Groebner
	// basis is equal to either of these to eliminate
	// trivial 0-dimensional solutions.
	groebner_zero := [C.k : k in [1..num_coeff]];
	groebner_identity := basis_domain eq basis_codomain select
		groebner_zero
	else
		[]
	;
	for i := 1 to n do
		for j := 1 to n do
			if i eq j and not IsEmpty(groebner_identity) then
				// If the bases are equal, the identity
				// matrix will be a possible solution.
				groebner_identity[k] -:= 1;
			end if;
			degree := M_grading[i][j];
			if degree ge 0 then
				terms := MonomialsOfDegree(CR, degree);
				m_ij := 0;
				for b := 1 to #terms do
					m_ij +:= (C.k) * terms[b];
					k +:= 1;
				end for;
				M[i][j] := m_ij;
			end if;
		end for;
	end for;
	
	// Create the system of equations.
	S := [];
	phi := hom<R -> CR | [CR.i : i in [1..Ngens(R)]]>;
	for i := 1 to #action_domain do
		S cat:= Eltseq(
			M*ChangeRing(action_domain[i], CR, phi) -
			ChangeRing(action_codomain[i], CR, phi)*M
		);
	end for;
	
	return C, CR, M, S, groebner_zero, groebner_identity;
	
end function;

procedure reduce(~S)
	// Currently, the expressions in S live inside CR.
	// Let p be any such polynomial expression. Clearly
	// p = 0 if and only if, for all d, the coefficient
	// of the degree d term is 0. This allows us to
	// reduce our system to a system of equations in C.
	// Another clever trick due to Victor.
	i := 1;
	while i le #S do
		if Degree(S[i]) gt 0 then
			monomial_coefficients := Coefficients(S[i]);
			S := S[1..i-1] cat monomial_coefficients cat S[i+1..#S];
			i +:= #monomial_coefficients;
		else
			i +:= 1;
		end if;
	end while;
end procedure;

// Solve for the idempotents of a given module.
// Returns a list of bases for the primitive idempotents.
procedure decompose(basis, action, ~primitives)

	n := #basis;

	// Build a general degree 0 morphism.
	// This function returns a ring of coefficients C,
	// the tensor product of C and R, a symbolic matrix
	// M representing a general degree 0 right R-module
	// homomorphism and a system of equations S that it
	// must satisfy to be a bimodule homomorphism.
	C, CR, M, S, groebner_zero, groebner_identity := morphism(
		basis, action, basis, action, 0
	);
	
	// Add the idempotent constraint.
	S cat:= Eltseq(M*M - M);
	// Reduce the system of equations from CR to C.
	reduce(~S);

	// Solve our system of equations.
	// I suspect this ideal should always
	// be radical, but I'm not sure why.
	I := ideal<C | S>;
	D := SAFE select PrimaryDecomposition(I) else RadicalDecomposition(I);
	// Build the idempotents array. This consists of pairs
	// of idempotent matrices E and bases for their images.
	idempotents := [];
	for J in D do
		// Performing PrimaryDecomposition invokes a computation of the
		// Groebner bases. We can reuse the ones it computed for us here
		// to ensure that this solution is neither zero nor the identity.
		// We expect (but do not assume) J to always be 0-dimensional
		// unless QB_s = Q(-1) + Q(1), as an analogue to how KL basis
		// elements multiply.
		G := GroebnerBasis(J);
		if G ne groebner_zero and G ne groebner_identity then
			// We have a new idempotent.
			// The Krull dimension of the ideal is the maximal cardinality of
			// the set of indeterminates in C such that there is no leading
			// monomial depending only on variables in C. The indeterminates
			// not in this set are our independent variables. We can determine
			// this set conveniently using Dimension and then feed the result
			// into VarietySequence to solve the new 0-dimensional system.
			d, U := Dimension(J);
			V := VarietySequence(J + ideal<C | [C.i : i in U]>)[1];
			E := ChangeRing(M, R,
				hom<CR -> R |
					hom<C -> F | V>,
					[R.i : i in [1..Ngens(R)]]
				>
			);
			// We save the rank of E (in other words, the trace)
			// so we can sort this array by rank before computing
			// primitive idempotents. Because the trace varies
			// continuously while ranks are discrete, we know that
			// the rank must be constant within each ideal J.
			Append(~idempotents,
				[* E, IntegerRing()!Trace(E), d, G *]
			);
		end if;
	end for;
	
	// If we found no non-trivial idempotents,
	// we must be indecomposable.
	if IsEmpty(idempotents) then
		return;
	end if;
	
	// The code below is messy and suboptimal.
	
	// The idempotents array will now be an array of 4-tuples
	// of the form (E, Tr(E), d, G), where E is an idempotent
	// matrix, d is the dimension of its corresponding ideal
	// and G is a Groebner basis for its corresponding ideal.
	
	// Sort the idempotents by rank (trace). This is
	// to prevent the situation where a non-primitive
	// idempotent splits into an indecomposable
	// that we haven't added to our dictionary yet.
	Sort(~idempotents, func<I1, I2 | I1[2] - I2[2]>);
	
	// Find the primitive idempotents.
	// We know the smallest idempotent, which will be the
	// first in our idempotents array, will be primitive.
	total_rank := idempotents[1][2];
	primitive_matrices := [* idempotents[1][1] *];
	// Projective modules over polynomial rings are free.
	// In other words, we can find a basis for the image of E.
	// The "Image" function in Magma computes the row space.
	// This basis fully encodes the indecomposable summand.
	primitives := [* MinimalBasis(Image(Transpose(primitive_matrices[1]))) *];
	i := 2;
	Z := ZeroMatrix(R, n);
	while total_rank lt n do
		// We essentially step through our idempotents from
		// smallest rank to largest, adding those that are
		// orthogonal until their ranks add up to n.
		if idempotents[i][3] eq 0 then
			// If the dimension of the ideal is 0, we're on easy street.
			is_primitive := true;
			for j := 1 to #primitive_matrices do
				if
					primitive_matrices[j]*idempotents[i][1] ne Z or
					idempotents[i][1]*primitive_matrices[j] ne Z
				then
					is_primitive := false;
					break;
				end if;
			end for;
			if is_primitive then
				E := idempotents[i][1];
				Append(~primitive_matrices, E);
				Append(~primitives, MinimalBasis(Image(Transpose(E))));
				total_rank +:= idempotents[i][2];
			end if;
		else
			// If the dimension of the ideal is non-zero,
			// things are a little trickier, since some
			// solutions may not be primitive with respect
			// to our initial choice of a primitive ideal.
			S := idempotents[i][4];
			for E in primitive_matrices do
				S cat:= Eltseq(
					M*ChangeRing(E, CR,
						hom<R -> CR | [CR.i : i in [1..Ngens(R)]]>
					)
				) cat Eltseq(
					ChangeRing(E, CR,
						hom<R -> CR | [CR.i : i in [1..Ngens(R)]]>
					)*M
				);
			end for;
			reduce(~S);
			I := ideal<C | S>;
			D := SAFE select
				PrimaryDecomposition(I)
			else
				RadicalDecomposition(I)
			;
			if not IsEmpty(D) then
				_, U := Dimension(D[1]);
				V := VarietySequence(D[1] + ideal<C | [C.i : i in U]>)[1];
				E := ChangeRing(M, R,
					hom<CR -> R |
						hom<C -> F | V>,
						[R.i : i in [1..Ngens(R)]]
					>
				);
				Append(~primitive_matrices, E);
				Append(~primitives, MinimalBasis(Image(Transpose(E))));
				total_rank +:= #primitives[#primitives];
			end if;
		end if;
		i +:= 1;
	end while;
	
end procedure;

// Reduce each rank r idempotent to a graded
// basis and a list of rxr action matrices.
function flatten(B, basis, action)
	
	new_basis := [];
	new_action := [];
	
	// Compute the degrees of the elements of B.
	for v in B do
		b := Eltseq(v);
		// Find the index of the first non-zero entry.
		i := 1;
		while i ne #b do
			if b[i] ne 0 then
				break;
			end if;
			i +:= 1;
		end while;
		// Assuming the basis vector is homogeneous, this is good enough.
		Append(~new_basis, 2*Degree(b[i])+basis[i]);
	end for;
	
	// In principle computing a basis for the image
	// of our idempotent will not preserve the order
	// of the basis, so we need to sort it again here.
	if SORT_BASES then
		ParallelSort(~new_basis, ~B);
	end if;
	
	// We want a projection P and an inclusion I such that
	// P*I = IdentityMatrix(R, #B). Then for each action
	// matrix A, all we need to do is compute P*A*I.
	// The injection is easy, since it just goes from the
	// standard basis into our new basis B.
	I := Transpose(Matrix(B));
	// This would be a lot nicer if Solution was implemented
	// for matrices over polynomial rings, but alas.
	P := [];
	zero_vector := Vector(R, [0 : i in [1..#B]]);
	for i := 1 to #B do
		ei := zero_vector;
		ei[i] := 1;
		Append(~P, Solution(I, ei));
	end for;
	P := Matrix(P);
	
	// Inject from E into QB_s, apply A, then project back.
	for A in action do
		Append(~new_action, P*A*I);
	end for;
	
	return new_basis, new_action;
	
end function;

// Let Q be a new, candidate indecomposable and Q' an
// indecomposable we have seen previously. This function
// determines whether Q(d) is isomorphic to Q' for some d.
function isomorphic(new_basis, new_action, basis, action)

	n := #new_basis;
	
	// Let (b_1, ..., b_n) be a basis for Q and
	// let (b_1', ..., b_m') be a basis for Q'.
	// First, make sure n = m.
	if n ne #basis then
		return false, 0;
	end if;
	
	// Our candidate may be a grading shift of Q'. We want an
	// isomorphism in Hom^0(Q(d), Q'), so we look for some d
	// such that d + deg(b_i) = deg(b_i') for all i. Because
	// deg(m_ij) = d + deg(b_j) - deg(b_i'), this means that
	// the diagonal elements will be degree d = 0 (scalars).
	sorted_new_basis := Sort(new_basis);
	sorted_basis := Sort(basis);
	d := sorted_basis[1] - sorted_new_basis[1];
	for i := 1 to n do
		// Shift the degree of the domain basis by d so we
		// only need to look for degree 0 morphisms.
		new_basis[i] +:= d;
		if d+sorted_new_basis[i] ne sorted_basis[i] then
			return false, 0;
		end if;
	end for;
	
	// Build a general degree 0 morphism.
	// This function returns a ring of coefficients C,
	// the tensor product of C and R, a symbolic matrix
	// M representing a general degree d right R-module
	// homomorphism and a system of equations S that it
	// must satisfy to be a bimodule homomorphism.
	C, _, M, S, groebner_zero, _ := morphism(
		new_basis, new_action, basis, action, SAFE select 1 else 0
	);
	
	if SAFE then
		// A clever trick due to Victor. When SAFE is set, C will
		// contain an additional coefficient that we will take to
		// represent 1/det(M), forcing det(M) to be invertible.
		S cat:= [Determinant(M)*C.Ngens(C) - 1];
	end if;
	// Reduce the system of equations from CR to C.
	reduce(~S);

	// Solve our system of equations.
	// When I is generated by a system of
	// linear equations it will be radical.
	I := ideal<C | S>;
	D := SAFE select PrimaryDecomposition(I) else RadicalDecomposition(I);
	for J in D do
		// We expect (but do not assume, unless the SAFE flag is set)
		// Hom^0(Q, Q') to be the ground field if Q is isomorphic to
		// Q' and 0 otherwise, as an analogue to the "almost-orthogonality"
		// of the KL basis. If the SAFE flag is unset, Victor's determinant
		// trick ensures that any non-zero solution will be an isomorphism.
		if GroebnerBasis(J) ne groebner_zero then
			return true, d;
		end if;
	end for;
	return false, 0;
	
end function;


//===========//
// Main Loop //
//===========//
// Recursively compute the indecomposable objects layer-by-layer.
function main()

	// Prepare a file to save the results.
	file := prepare_output();
	
	// Keep a dictionary of indecomposable objects sorted by layer.
	// We encode endecomposables as a graded basis
	// together with a tuple of action matrices.
	// We actually only store the graded degrees of
	// each basis element; the actual basis is
	// secretly encoded in the action matrix.
	dictionary_bases := [[* *]];
	dictionary_actions := [[* *]];
	
	// We also keep track of where each indecomposable came from;
	// that is, if Q was seen as a summand of Q'*B_{s_k}, we store
	// k so that we know not to bother computing Q*B_{s_k}.
	layer_origins := [];
	
	// Maintain a W-graph with our findings.
	// Each element is a quadruple of integers (s, t, k, d).
	//     s = the index in our dictionary of the source indecomposable;
	//     t = the index in our dictionary of the target indecomposable;
	//     k = the index of the simple reflection associated with the edge;
	//     d = the grading shift of the summand relative to the target.
	// In other words, an edge encodes some indecomposable
	// Q_t(d) appearing as a direct summand of Q_s*B_{s_k}.
	W_graph := [];
	
	// Get a set of right coset representatives for WK\W.
	// These are used when building the generating standard bimodules.
	KW := [];
	if IsEmpty(WK) then
		WFP := CoxeterGroup(GrpFPCox, W);
		KW := [[0]];
	else
		WFP := CoxeterGroup(GrpFPCox, W);
		KW := [Eltseq(w) : w in RightTransversal(WFP, sub<WFP | WK>)];
	end if;
	
	// Compute the invariant ring RK.
	// Our objects are (RK, R)-bimodules.
	RK := ChangeUniverse(PrimaryInvariants(InvariantRing(
		sub<W | [&*[W.k : k in WK[i]] : i in [1..#WK]]>
	)), R);
	
	// Add the standard bimodules to our dictionary.
	for word in KW do
		Append(~dictionary_bases[1], [0]);
		Append(~dictionary_actions[1], []);
		Append(~layer_origins, [0]);
		for generator in RK do
			A := Matrix(R, 1, 1, [generator]);
			for k := 1 to #word do
				if word[k] gt 0 then
					A[1][1] := s(word[k], A[1][1]);
				end if;
			end for;
			Append(~dictionary_actions[1][#dictionary_actions[1]], A);
		end for;
	end for;
	
	// Keep track of the number of indecomposables
	// in each layer for identification purposes
	// when building the W-graph.
	num_ind := [0, #KW];
	
	// Build our dictionaries layer-by-layer until we
	// encounter a layer with no new indecomposables.
	layer := 1;
	while not IsEmpty(layer_origins) do
	
		Append(~dictionary_bases, [* *]);
		Append(~dictionary_actions, [* *]);
		Append(~num_ind, num_ind[#num_ind]);
		
		next_layer_origins := [];
		
		// For each indecomposable Q_{source} on the current layer,
		// tensor it with B_{s_k} and find its indecomposable summands.
		for source := 1 to #layer_origins do
			for k := 1 to Ngens(R) do
			
				// If this indecomposable came from tensoring with
				// B_{s_k}, don't bother tensoring with B_{s_k} again.
				for i in layer_origins[source] do
					if i eq k then
						// Add some splitting edges to
						// the W-graph and skip s_k.
						Append(~W_graph, [
							num_ind[layer]+source, num_ind[layer]+source, k, 1
						]);
						Append(~W_graph, [
							num_ind[layer]+source, num_ind[layer]+source, k, -1
						]);
						continue k;
					end if;
				end for;
				
				// Tensor the source indecomposable
				// Q_{source} on the right by B_{s_k}.
				basis, action := tensor(k,
					dictionary_bases[layer][source],
					dictionary_actions[layer][source]
				);
				// Decompose Q_{source}*B_{s_k} and
				// find the primitive idempotents.
				// This will be an array of pairs of
				// idempotent matrices with bases for
				// their images.
				primitives := [];
				decompose(basis, action, ~primitives);
				
				new_bases := [* *];
				new_actions := [* *];
				if IsEmpty(primitives) then
					// If we only found the identity idempotent,
					// the current module is indecomposable.
					Append(~new_bases, basis);
					Append(~new_actions, action);
				else
					// Reduce our idempotents to a graded basis and some
					// rxr action matrices, where r is their rank.
					for B in primitives do
						new_basis, new_action := flatten(
							B, basis, action
						);
						Append(~new_bases, new_basis);
						Append(~new_actions, new_action);
					end for;
				end if;
				
				// Prune our list of idempotents by removing indecomposables
				// that are isomorphic to ones we've already seen.
				i := 1;
				while i le #new_actions do
					
					// We only compare with indecomposables from the
					// layers adjacent to the source indecomposable.
					prune := false;
					// I believe we only have to loop from
					// Maximum(1, layer-1) to layer+1, but
					// perhaps for exotic groups weird stuff
					// could happen.
					for target_layer := 1 to layer+1 do
						for target := 1 to #dictionary_actions[target_layer] do
							are_isomorphic, d := isomorphic(
								new_bases[i],
								new_actions[i],
								dictionary_bases[target_layer][target],
								dictionary_actions[target_layer][target]
							);
							if are_isomorphic then
								// Update the W-graph and exit from the loop.
								Append(~W_graph, [
									num_ind[layer]+source,
									num_ind[target_layer]+target,
									k,
									d
								]);
								// If this indecomposable is from the
								// next layer, update next_layer_origins.
								if target_layer eq layer+1 then
									Append(~next_layer_origins[target], k);
								end if;
								Remove(~new_bases, i);
								Remove(~new_actions, i);
								prune := true;
								// Exit from both loops.
								break target_layer;
							end if;
						end for;
					end for;
					
					// If this is a genuinely new indecomposable,
					// update the W-graph and increment i.
					if not prune then
						// Update W-graph here!
						num_ind[#num_ind] +:= 1;
						Append(~W_graph, [
							num_ind[layer]+source, num_ind[#num_ind], k, 0
						]);
						Append(~next_layer_origins, [k]);
						i +:= 1;
					end if;
					
				end while;
				
				// Update our dictionary of indecomposables.
				dictionary_bases[layer+1] cat:= new_bases;
				dictionary_actions[layer+1] cat:= new_actions;
				
			end for;
		end for;
		
		layer +:= 1;
		layer_origins := next_layer_origins;
		
	end while;
	
	Prune(~dictionary_bases);
	Prune(~dictionary_actions);
	
	Write(file, dictionary_bases);
	Write(file, dictionary_actions);
	Write(file, W_graph);
	"Success! Output written to " cat file cat ".";
	
	return dictionary_bases, dictionary_actions, W_graph;
	
end function;

main();