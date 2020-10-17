/**
 * Author: Simon Lindholm
 * Date: 2020-10-17
 * Source: http://www.inf.fu-berlin.de/lehre/SS13/AG/randinc3d.pdf
 * Description: Computes all faces of the 3-dimension hull of a point set.
 * \begin{enumerate}
 *   \item \texttt{verts} gives vertices of each triangle, in ccw order seen from outside.
 *   \item \texttt{edges[i]} is the adjacent triangle when crossing the (vertex i+1, vertex i+2) edge.
 * \end{enumerate}
 * Time: expected O(N log N)
 * Status: TODO stress-test and SPOJ CH3D
 *
 * Details:
 * The basic algorithm is the following:
 * - Shuffle the input points randomly, making sure the first four points are
 *   in general position. Set up a tetrahedron from them.
 * - For all other points, try to find an arbitrary triangle that it lies
 *   outside of ("conflicts with"), i.e. which should be removed when the point
 *   is added. Keep these in list 'dep', plus a reverse list 'rdep' from
 *   triangle to points.
 * - Loop over the other points, adding them one by one if they have a conflict
 *   triangle (points without conflict triangles are not in the hull). A point
 *   can have multiple conflict triangles, and we can find them all by
 *   performing a BFS from dep[i]. Create new triangles from the new point and
 *   the border of the BFS'd region. (At this point, we have edges pointing
 *   from removed triangle -> new triangle -> border triangle -> new triangle.)
 *   This part takes O(n) time in total, in expectation.
 * - For all removed triangles, recompute conflict triangles for the points in
 *   rdep[]. This is done by a BFS over the set of removed triangles plus the
 *   newly added ones, looking at only conflict triangles, starting from the
 *   known conflict triangle. This part takes O(n log n) time.
 * - Finally, reindex back into input coordinates.
 *
 * We keep the following state:
 * - 'pi': a random permutation of 0..N, such that ps[pi[0..4]] (used as the
 *   starting tetrahedron) are in general position.
 * - 'pp': pp[i] = ps[pi[i]]. This is an optimization to reduce indirection.
 * - 'tris': a buffer of triangle hull faces, some of which are live. Unused
 *   triangles are kept in a freelist `free'. In each step we may need up to 2N
 *   triangles: V-E+F=2, E=3/2*F, F = 2V-4 < 2N. Since both removed and new
 *   triangles are live at once, we may need twice that temporarily (or perhaps
 *   only 1.5x? but 4N is cheap enough). Hence, we give it size T = 4*N. The
 *   triangle with index 0 is never used, to get nice sentinel for dep[], and
 *   to help the partial_sum-based reindexing at the end.
 * - 'free': a stack of unused triangles, with logical size 'fend'. It does
 *   contain 0, to make the loop at the end work, but it's at the bottom of the
 *   stack and will never be used.
 * - 'dep', 'rdep': explained above.
 * - 'X': when removing the triangles bounded by the cycle Z, and introducing
 *   new ones for all edges on the cycle, X[vert] = tri1 ^ tri2 where vert is a
 *   vertex of the cycle, and tri1 and tri2 are the two newly added triangles.
 *   This helps the triangles find each other. At the start of each loop
 *   iteration, X will be all zero.
 * - 'seen': when performing BFS's/DFS's, this keeps track of which triangles
 *   have been seen; ones unseen have seen[i] < time. time increments for each
 *   search.
 * - 'q': queue for the initial BFS. Each triangle is added just once into the
 *   queue, at the same time as marking it seen. 'qe' marks the end of the
 *   queue. The queue is later traversed to recompute conflict triangles, which
 *   is why we cannot reuse the same queue for the DFS's, and why we cannot use
 *   a DFS for the first traversal.
 * - 's': stack for the subsequent DFS's. 'e' marks the end.
 * - 'ren': mapping from sparse triangle indices to dense ones that we return.
 */
#pragma once

struct Tri { array<int, 3> verts, edges; };

vector<Tri> hull3d(const vector<Point3D<double>>& ps) {
	int N = sz(ps), T = 4 * N, time = 0, fend = 1, p = 2, tri = 4;
	auto pp = ps;
	vi pi(N), X(N), dep(N), seen(T), free(T), q(T), s(T), ren(T, 1);
	vector<vi> rdep(T);
	vector<Tri> tris(T), v;
	rep(i,0,4) rep(j,0,3)
		++(tris[i+1].edges[j] = tris[i+1].verts[j] = i ^ (j + 1));
	iota(all(pi), 0);
	while (!(ps[p] - ps[0]).cross(ps[1] - ps[0]).dist2()) p++; // TODO: don't use dist2()
	pp[2] = pp[p]; swap(pi[p++], pi[2]);
#define PT(i) (pp[tris[tri].verts[i]] - pp[p])
	auto outside = [&](int tri, int p) {
		return PT(0).cross(PT(1)).dot(PT(2)) < 0; // TODO: int128?
	};
	while (!PT(0).cross(PT(1)).dot(PT(2))) p++, assert(p < N); // TODO: int128?
	swap(pi[3], pi[p]);
	if (outside(tri, p)) swap(pi[0], pi[1]);
	random_shuffle(4 + all(pi));
	rep(i,0,N) pp[i] = ps[pi[i]];
	rep(i,5,T) free[fend++] = i;
	rep(i,0,4) rep(j,4,N) if (!dep[j] && outside(i, j))
		dep[j] = i, rdep[i].push_back(j);
	rep(j,4,N) if (dep[j]) {
		for (int x : X) assert(!x);
		int t = q[0] = dep[j], qe = 1, origInd = fend;
		seen[t] = ++time;
		assert(outside(q[0], j));
		rep(qi,0,qe) rep(ei,0,3) {
			int t = q[qi], &t2 = tris[t].edges[ei];
			if (seen[t2] == time) continue;
			if (outside(t2, j)) { seen[q[qe++] = t2] = time; continue; }
			int newTri = free[--fend];
			rdep[newTri].clear();
			Tri& tr = tris[newTri];
			tr.verts[0] = j;
			tr.edges[0] = t2;
			rep(i,1,3) tr.verts[i] = tris[t].verts[(ei+i) % 3];
			rep(i,1,3) X[tr.verts[i]] ^= newTri;
			replace(all(tris[t2].edges), t, newTri);
			t2 = newTri;
		}
		rep(i,fend,origInd) {
			int t = free[i], &x = X[tris[t].verts[1]];
			tris[tris[t].edges[2] = t ^ x].edges[1] = t;
			x = 0;
		}
		rep(qi,0,qe) free[fend++] = q[qi];
		rep(qi,0,qe) for (int x : rdep[q[qi]]) if (x != j) {
			int e = 1; s[0] = dep[x];
			assert(outside(dep[x], x));
			seen[dep[x]] = ++time;
			dep[x] = 0;
			while (e-- && tris[s[e]].verts[0] != j) // TODO: could also check "isOld[s[e]]"
				for (int t : tris[s[e]].edges)
					if (seen[t] < time && outside(t, x))
						s[e++] = t, seen[t] = time;
			if (e != -1) rdep[dep[x] = s[e]].push_back(x);
		}
	}
	rep(i,0,fend) ren[free[i]] = 0;
	partial_sum(all(ren), ren.begin());
	v.resize(ren.back());
	rep(i,1,T) if (ren[i] != ren[i - 1]) {
		for (int& x : tris[i].edges) x = ren[x - 1];
		for (int& x : tris[i].verts) x = pi[x];
		v[ren[i - 1]] = tris[i];
	}
	return v;
}
