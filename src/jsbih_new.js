/****************************************************************************** 
	jsbih.js - General-Purpose Non-Recursive Bounding-Interval Hierarchy Library
	Version 0.2.1, April 7th 2010

  Copyright (c) 2010 Jon-Carlos Rivera

  This software is provided 'as-is', without any express or implied
  warranty.  In no event will the authors be held liable for any damages
  arising from the use of this software.

  Permission is granted to anyone to use this software for any purpose,
  including commercial applications, and to alter it and redistribute it
  freely, subject to the following restrictions:

  1. The origin of this software must not be misrepresented; you must not
     claim that you wrote the original software. If you use this software
     in a product, an acknowledgment in the product documentation would be
     appreciated but is not required.
  2. Altered source versions must be plainly marked as such, and must not be
     misrepresented as being the original software.
  3. This notice may not be removed or altered from any source distribution.

	Jon-Carlos Rivera - imbcmdth@hotmail.com
******************************************************************************/
var isArray = function(o) {
	return Object.prototype.toString.call(o) === '[object Array]'; 
};

/**
 * ITree - A simple interval-tree structure for great results.
 * @constructor
 */
var jsBIH = function(dimensions){
	// Variables to control tree

	// Number of "interval pairs" per node
	var _Dimensions = 2;
	if(!isNaN(dimensions)){ _Dimensions = dimensions;}
	var _Max_Leaf_Size = 9;
	var _make_Empty = function() {
		var i, d = [];
		for( i = 0; i < _Dimensions; i++ ) {
			d.push({a:0, b:0});
		}
		return d;
	};

	var _make_Intervals = function(intervals, d) {
		var i;
		if(!isArray(d))
			d = [];
		for( i = 0; i < _Dimensions; i++ ) {
			d[i] = {a:intervals[i].a, b:intervals[i].b};
		}
		return d;
	};

    // Nodes:
	// ir - "specifier" - the interval bounds of the data in the "l" node along the "x"
	// il - "specifier" -  the interval bounds of the data in the "r" node along the "x"
	// x - "axis" - numeric dimension to specify the axis of this node.
	// l - "left" (or "less") - a node or an item
	//   - the object(s) in this tree with a smaller value along the current axis
	// r - "right" -  a node or an item
	//   - the object(s) in this tree with a larger value along the current axis
    // Items:
	// i - "specifier" - an array of intervals forming a minimally bounding volume for the
	//   - element contained in "o"
	// o - "object" - a reference to an object.

	//node = 	{il:{a:0,b:0}, ir:{a:0,b:0}, x:0, l:null, r:null };
	//node =    [ 0, 0, 0, 0, 0, null, null];  For speed??

	// Start with an empty tree
	var _T = null; // The tree iteself
	var _E = null; // The entire tree's envelope

    // The last bounding volume calculated during "optimized" removal
    // Only interesting for debugging and educational display purposes 
    var _last_bb = null;
	/* expands intervals A to include intervals B, intervals B is untouched
	 * [ rectangle a ] = expand_rectangle(rectangle a, rectangle b)
	 * @static function
	 */
	var _expand_Interval = function(a, b)	{
		var i, n;
		n = Math.min(a.a, b.a);
		a.b = Math.max(a.a+a.b, b.a+b.b) - n;
		a.a = n;
		return a;
	};

	/* expands intervals A to include intervals B, intervals B is untouched
	 * [ rectangle a ] = expand_rectangle(rectangle a, rectangle b)
	 * @static function
	 */
	var _expand_Intervals = function(a, b)	{
		var i, n, aa, ab, ba, bb;
		if(!a) {
		    a = _make_Empty();
            for( i = 0; i < _Dimensions; i++ )
            {
                a[i].a = b[i].a;
                a[i].b = b[i].b;
            }
		} else {
          //  if( a.length != _Dimensions || b.length != _Dimensions ) { return false; } // Should probably be an error.
            for( i = 0; i < _Dimensions; i++ )
            {
                _expand_Interval(a[i], b[i]);
            }
		}
		return a;
	};

	/* returns true if intervals "a" overlaps intervals "b"
	 * [ boolean ] = overlap_intervals(intervals a, intervals b)
	 * @static function
	 */
	var _overlap_intervals = function(a, b) {
		var i, ret_val = true;
		if( a.length != _Dimensions || b.length != _Dimensions ) { ret_val = false; } // Should probably be an error.
		for( i = 0; i < _Dimensions; i++ )
		{
			ret_val = ret_val && (a[i].a < (b[i].a+b[i].b) && (a[i].a+a[i].b) > b[i].a);
		}
		return ret_val;
	};

    var _overlap_left = function(intervals, node) {
		return (intervals[node.x].a <= node.il);
    }

    var _overlap_right = function(intervals, node) {
		return (intervals[node.x].a + intervals[node.x].b >= node.ir);
    }

	var _overlap_interval = function(a, b) {
		return (a.a < (b.a+b.b) && (a.a+a.b) > b.a);
	};

	/* generates a minimally bounding intervals for all intervals in
	 * array "nodes". If intervals is set, it is modified into the MBV. Otherwise,
	 * a new set of intervals is generated and returned.
	 * [ rectangle a ] = make_MBR(rectangle array nodes, rectangle rect)
	 * @static function
	 */
	var _make_MBV = function(nodes, intervals) {
		var d = 0;
		if(nodes.length < 1)
		{
			//throw "_make_MBV: nodes must contain at least one object to bound!";
			return _make_Empty();
		}

		if(!intervals) {
			intervals = _make_Intervals(nodes[0].i);
			d = 1;
		}
		/*else {
			_make_Intervals(nodes[0].i, intervals);
		}*/

		for(var i = nodes.length - 1; i >= d; i--) {
			_expand_Intervals(intervals, nodes[i].i);
		}

		return(intervals);
	};

    var _choose_Left = function(item, node){
        if( item.i[node.x].a + item.i[node.x].b <= node.il) return true;
        if( item.i[node.x].a >= node.ir) return false;
        var delta_size_left = (item.i[node.x].a + item.i[node.x].b) - node.il;
        var delta_size_right = node.ir - item.i[node.x].a;
        return(delta_size_left <= delta_size_right);
    };

	var _make_Node = function(item_a, item_b){
		var left = new Array(_Dimensions);
		for(i = 0; i < _Dimensions;i++)	left[i] = item_a;
		var right = new Array(_Dimensions);
		for(i = 0; i < _Dimensions;i++)	right[i] = item_b;
        var t1, t2, l, i, d;

        for(i = 0; i < _Dimensions;i++)	{
            if( item_a.i[i].a < item_b.i[i].a ) {
                left[i] = item_a;
                right[i] = item_b;
            }
            else {
                left[i] = item_b;
                right[i] = item_a;
            }
        }

		d = 0;
		var outer_difference, last_outer_difference = 0;
		var difference, last_difference = 0;
		for(i = 0; i < _Dimensions;i++)	{
			difference = Math.max(left[i].i[i].a + left[i].i[i].b, right[i].i[i].a + right[i].i[i].b) - left[i].i[i].a;
			if(difference > last_difference)
			{
				d = i;
				last_difference = difference;
			}
		}
        var new_node = {
            il: left[d].i[d].a + left[d].i[d].b,
            ir: right[d].i[d].a,
            x: d,
            l: left[d],
            r: right[d] 
            };
		return( new_node );
	};

// Intersect with overall tree bounding-box
// Returns a segment contained within the pointing box
var _intersect_E = function(ray, box) {
    if(!box) {
        box = _E; // By default, use the scene bounding box
    }
    var i, j;
    var parameters = [[],[]];
    // inv_direction and sign can be pre-computed per ray
    var inv_direction = [];
    var sign = [];

    // Initialize values
    for( i = 0; i < _Dimensions; i++ ){
        parameters[0].push(box[i].a);
        parameters[1].push(box[i].a + box[i].b);

        j = 1 / ray[i].b;
        inv_direction.push(j);
        sign.push((j <= 0)?1:0);
    }

    var omin, omax, tmin, tmax;
    var tmin_a, tmin_b, tmax_a, tmax_b;

    omin = (parameters[sign[0]][0] - ray[0].a) * inv_direction[0];
    omax = (parameters[1-sign[0]][0] - ray[0].a) * inv_direction[0];

//if(isNaN(omin) || isNaN(omax)) throw "o1: NAN!";

/*    tmin_a = Math.min(omin, Infinity); tmin_b = Math.max(omin, -Infinity);
    tmax_a = Math.min(omax, Infinity); tmax_b = Math.max(omax, -Infinity);
    omin = Math.min(tmin_a, tmin_b);
    omax = Math.max(tmax_a, tmax_b);    */


    for( i = 1; i < _Dimensions; i++ ) {
        tmin = (parameters[sign[i]][i] - ray[i].a) * inv_direction[i];
        tmax = (parameters[1-sign[i]][i] - ray[i].a) *inv_direction[i];

//if(isNaN(tmin) || isNaN(tmax) || isNaN(inv_direction[i])) throw "t: NAN!";

/*        tmin_a = Math.min(tmin, Infinity); tmin_b = Math.max(tmin, -Infinity);
        tmax_a = Math.min(tmax, Infinity); tmax_b = Math.max(tmax, -Infinity);
        tmin = Math.min(tmin_a, tmin_b);
        tmax = Math.max(tmax_a, tmax_b);  */

        if ( (omin > tmax) || (tmin > omax) ) {
            return false;
        }
        if (tmin > omin) {
            omin = tmin;
        }
        if (tmax < omax) {
            omax = tmax;
        }
//if(isNaN(omin) || isNaN(omax)) throw "o2: NAN!";
    }

    if( omin >= Infinity || omax <= -Infinity )
    {
//        throw "Gevalt!";
        return false;
    }
    if( omin < 0 && omax < 0) return false;
    if( omin < 0 ) omin = 0;

    var rs = _make_Empty();

    for( i = 0; i < _Dimensions; i++ ) {
        rs[i].a = ray[i].a + ray[i].b * omin;
        rs[i].b = ray[i].a + ray[i].b * omax;
    }

    return( rs );
};

var _clip_Ray_Start = function(ray, axis, split_plane){
    // The ray enters the volume between the planes so
    // we need to clip the ray start for this case
    var tdist = (split_plane - ray[axis].a) / (ray[axis].b - ray[axis].a);
   // if(tdist < 0 ) throw "What!";
    var ret_rs = [];
    for(var i = 0; i < _Dimensions; i++) {
        if(i !== axis) {
            ret_rs.push({a:ray[i].a + (ray[i].b - ray[i].a) * tdist, b:ray[i].b});
        } else {
            ret_rs.push({a:split_plane, b:ray[i].b});
        }
     }
    return ret_rs;
};


var _clip_Ray_End = function(ray, axis, split_plane){
    // The ray exits the volume between the planes so
    // we need to clip the ray end for this case
    var tdist = (split_plane - ray[axis].a) / (ray[axis].b - ray[axis].a);
   // if(tdist < 0 ) throw "What!";
    var ret_rs = [];
    for(var i = 0; i < _Dimensions; i++) {
        if(i !== axis) {
            ret_rs.push({a:ray[i].a, b:ray[i].a + (ray[i].b - ray[i].a) * tdist});
        } else {
            ret_rs.push({a:ray[i].a, b:split_plane});
        }
     }
    return ret_rs;
};

this.intersect_ray = _intersect_E;

	/* generates a minimally bounding intervals for all intervals in
	 * array "nodes". If intervals is set, it is modified into the MBV. Otherwise,
	 * a new set of intervals is generated and returned.
	 * [ list of intersection objects ] = _intersect_subtree(options)
	 * @static function
	 */
// Based on Havran's TA-B -
// Modified for BIH with several new cases:
//  - I1 (ray enters between planes, exits in left node)
//  - I2 (ray enters between planes, exits in right node)
//  - I3 (ray enters between planes, exits between planes)
//  - B1 (Ray enters in both planes, exits both)
//  - B2 (Ray enters in both planes, exits left)
//  - B3 (Ray enters in both planes, exits right)
    var _intersect_subtree = function(options){
		var hit_stack = []; // Contains the nodes that overlap
		var ray_stack = []; // Contains the ray-segment for the current sub-tree
		var ray = options.ray;
		var return_node = options.return_nodes;
		var return_array = options.return_array;
		var root = options.root;
        var node = null;
        var rs = null;
        var axis = null;
        var new_rs = null;
        var tdist = null;
        var intersect_points;

        // Test ray AABB first
        rs = _intersect_E(ray);

//        if( rs != false ) {
      //      rs = rs.ray_segment;
//        } else { rs = null; }

        // If there are no elements or the ray-AABB test failed, don't bother traversing
		if( root !== null && rs !== false ){
		    hit_stack.push(root);
            ray_stack.push(rs);
		}

		while(hit_stack.length > 0) {
            node = hit_stack.pop(); // Depth-First Descent
            rs = ray_stack.pop(); // Depth-First Descent
                if("x" in node) { // A node!
                  axis = node.x; // Axis: 0 = x, 1 = y, 2 = z ...
                  // Cases where entry point is between *both* splitting planes
                  if( rs[axis].a < node.ir && rs[axis].a > node.il ) {
                    if( rs[axis].b <= node.il ) { // Is the exit point inside the left node?
                        /* case I1 */
                        // The ray enters the volume between the planes so
                        // we need to clip the ray start for this case
                        new_rs = _clip_Ray_Start(rs, axis, node.il);

                        hit_stack.push(node.l);
                        ray_stack.push(new_rs);
                    } else if( rs[axis].b >= node.ir ) { // Is the exit point inside the right node?
                        /* case I2 */
                        // The ray enters the volume between the planes so
                        // we need to clip the ray start for this case
                        new_rs = _clip_Ray_Start(rs, axis, node.ir);

                        hit_stack.push(node.r);
                        ray_stack.push(new_rs);
                    } // If start is between both planes,
                      // the end point CAN NOT be in BOTH nodes - it is unpossible
                      continue;
                 }
                  if( rs[axis].a <= node.il ) { // Starts in left node
                    if( rs[axis].a >= node.ir ) { // Also in right node!
                        // If we exit and are no longer in the right node, we must clip the ray
                        if( rs[axis].b < node.ir ) {
                            new_rs = _clip_Ray_End(rs, axis, node.ir);
                        } else {
                            new_rs = rs;
                        }
                        // This will be popped later, so right = far node
                        hit_stack.push(node.r);
                        ray_stack.push(new_rs);

                        // If we exit and are no longer in the left node, we must clip the ray
                        if( rs[axis].b > node.il ) {
                            new_rs = _clip_Ray_End(rs, axis, node.il);
                        } else {
                            new_rs = rs;
                        }
                        // This will be popped first, so left = near node
                        hit_stack.push(node.l);
                        ray_stack.push(new_rs);
                        continue;
                    }
                    if( rs[axis].b < node.ir ) { // We are exiting before the right plane
                        if( rs[axis].b <= node.il ) {
                            // We are exiting before the left plane
                            /* cases N1,N2,N3,P5,Z2,Z3 */
                            hit_stack.push(node.l);
                            ray_stack.push(rs);
                        } else {
                            // The ray exits the volume between the planes so
                            // we need to clip the ray end for this case
                            new_rs = _clip_Ray_End(rs, axis, node.il);

                            hit_stack.push(node.l);
                            ray_stack.push(new_rs);
                        }
                    } else { // The ray exits on the far side of the right plane
                        /* case N4 */
                        // This will be popped later, so right = far node
                        new_rs = _clip_Ray_Start(rs, axis, node.ir);

                        hit_stack.push(node.r);
                        ray_stack.push(new_rs);

                        // This will be popped first, so left = near node
                        new_rs = _clip_Ray_End(rs, axis, node.il);

                        hit_stack.push(node.l);
                        ray_stack.push(new_rs);
                    }
                    continue;
                  }
                  if( rs[axis].a >= node.ir ) { // Starts in right node
                    if( rs[axis].b > node.il ) { // Ray exits before the left plane
                        if( rs[axis].b >= node.ir ) { // Ray exits before the right plane
                            /* cases P1,P2,P3,N5,Z1 */
                            hit_stack.push(node.r);
                            ray_stack.push(rs);
                        } else {
                            /* cases P1,P2,P3,N5,Z1 */

                            // we need to clip the ray end for this case
                            new_rs = _clip_Ray_End(rs, axis, node.ir);
                            hit_stack.push(node.r);
                            ray_stack.push(new_rs);
                        }
                    } else {  // Ray hits both planes
                        /* case P4 */
                        // This will be popped later, so left = far node
                        new_rs = _clip_Ray_Start(rs, axis, node.il);
                        hit_stack.push(node.l);
                        ray_stack.push(new_rs);

                        // This will be popped first, so right = near node
                        new_rs = _clip_Ray_End(rs, axis, node.ir);
                        hit_stack.push(node.r);
                        ray_stack.push(new_rs);
                    }
                  }
                  continue;
              }  else if("n" in node) { // A collect of leaves!!
              	for( var ni = node.n.length-1; ni >= 0; ni--){
                  intersect_points = _intersect_E(ray, node.n[ni].i);
                  if( intersect_points != false ) {
                  var tmin = (intersect_points[0].a-ray[0].a)/ray[0].b;
                    if( !return_node ) {
                        return_array.push({intersect:tmin, object:node.n[ni].o});
                    } else {
                        return_array.push({intersect:tmin, object:node.n[ni]});
                    }
                  }
                }
              }
        }
		return(return_array);
    };

 	/* non-recursive internal remove function
	 * [object | false] = _remove_subtree( options )
	 * @private
	 * returns true if an element was deleted
	 * returns false if nothing was deleted
	 */
	var _remove_subtree = function(options) {
		var hit_stack = []; // Contains the nodes that overlap
		var parent_stack = []; // Contains parents of the current traversal
		var parent_count = []; // Contains parents of the current traversal
		var intervals = options.intervals;
		var optimized_remove = options.optimized_remove;
		var target_object = options.object;
		var root = options.root;
		var comparators = options.comparators;
        var deleted_object = false;
        var node = null;
        var last_node = null; // Used during the walk up.
        var BV = {minimal:null};

        var leaf_func = (function(BV) {
                   return (function(local_node) {
                        BV.minimal = _expand_Intervals( BV.minimal, local_node.i);
                   });
                })(BV);

        var yield_options = {
            comparators:{ // Since we want EVERY leaf, we just return true for all comparisons
                overlap_intervals: function(){ return true; },
                overlap_left: function(){ return true; },
                overlap_right: function(){ return true; }
            },
            yield:{
                leaf: leaf_func,
                node: function(local_node) { } 
            }
        };

		if( root != null ){
		    node = root;
		} else {
		    return false;
		}
			
		// This loop traverses the tree downward until an element is found or it returns unsuccessfully.
		while(node != null) {
          if("o" in node) { // A leaf!!
              if( (target_object == false && comparators.overlap_intervals(intervals, node.i))
               || (target_object != false && node.o === target_object) ) {
                   // Remove node and start walking up the tree
                   var parent = parent_stack.pop();
                   var grand_parent = parent_stack.pop();
                   if(!parent) {
                       _T = null; // There are NO other elements, make root null.
                       return node;
                   } else if(!grand_parent) {
                       // There is only one side to the tree now, make that first node the root.
                        if( node === parent.l) {
                          _T = parent.r;
                        } else {
                          _T = parent.l;
                        }
                       return node;
                   } else {
                       deleted_object = node;
                       if( grand_parent.l === parent ){
                       // replace grandparent.l with parent.not_me using current_side
                           if( node === parent.l) {
                              grand_parent.l = parent.r;
                              last_node = parent.r;
                              if( optimized_remove ) {
                                  yield_options.root = parent.r;
                                  yield_options.return_array = [];
                                  _yield_to( yield_options );
                              }
                            } else {
                              grand_parent.l = parent.l;
                              last_node = parent.l;
                              if( optimized_remove ) {
                                  yield_options.root = parent.l;
                                  yield_options.return_array = [];
                                  _yield_to( yield_options );
                              }
                            }
                       // resize grandparent.il if possible
                       } else {
                       // replace grandparent.r with parent.not_me using current_side
                           if( node === parent.l) {
                              grand_parent.r = parent.r;
                              last_node = parent.r;
                              if( optimized_remove ) {
                                  yield_options.root = parent.r;
                                  yield_options.return_array = [];
                                  _yield_to( yield_options );
                              }
                            } else {
                              grand_parent.r = parent.l;
                              last_node = parent.l;
                              if( optimized_remove ) {
                                  yield_options.root = parent.l;
                                  yield_options.return_array = [];
                                  _yield_to( yield_options );
                              }
                            }
                       }
                       parent_stack.push(grand_parent);
                       break; // Start walk up the tree
                       //return node;
                   }
              } else if( hit_stack.length > 0 ) { // Nothing at this level overlaps, so we climb up to the last-saved right node
                node = hit_stack.pop(); // This is always a right node
                parent_stack = parent_stack.slice(0, parent_count.pop()); // We need to trim any unneeded elements from our parent_stack
              } else { // We ain't found shit!
                return false;
              }
          } else if("x" in node) { // A node!
            parent_stack.push(node);
            if( intervals[node.x].a <= node.il ) {  // If left node overlaps..
                if( (intervals[node.x].a + intervals[node.x].b) >= node.ir ) { // If right overlaps too
                    parent_count.push(parent_stack.length); // Save the right node's parents for later
                    hit_stack.push(node.r); // Save the right node for later
                }
                node = node.l; // Make left node the current node
            } else if( (intervals[node.x].a + intervals[node.x].b) >= node.ir ) { // Just the right node overlaps
                node = node.r; // Make right node
            } else if( hit_stack.length > 0 ) { // Nothing at this level overlaps, so we climb up to the last-saved right node
                node = hit_stack.pop(); // This is always a right node
                parent_stack = parent_stack.slice(0, parent_count.pop()); // We need to trim any unneeded elements from our parent_stack
            } else { // We ain't found shit!
              return false;
            }
          }
       } // Done walking down the tree...
       if( optimized_remove ) {
        // Now start walking back UP the tree, resizing (shrinking) the nodes as needed.
        while( parent_stack.length > 1 ) {
            node = parent_stack.pop();
            if( last_node === node.l ) { // The left side's MBV is already calculated
                if(node.il > BV.minimal[node.x].a + BV.minimal[node.x].b) {
                    node.il = BV.minimal[node.x].a + BV.minimal[node.x].b;
                }
                yield_options.root = node.r;
                _yield_to( yield_options );
            } else if( last_node === node.r ) { // The right side's MBV is already calculated
                if(node.ir < BV.minimal[node.x].a ) {
                    node.ir = BV.minimal[node.x].a;
                }
                yield_options.root = node.l;
                _yield_to( yield_options );
            }
            last_node = node;
        }
        
        // Fix up the last (root) element
        node = parent_stack.pop();
        if( last_node === node.l ) {
            if(node.il > BV.minimal[node.x].a + BV.minimal[node.x].b) {
                node.il = BV.minimal[node.x].a + BV.minimal[node.x].b;
            }
        } else if( last_node === node.r ) {
            if(node.ir < BV.minimal[node.x].a ) {
                node.ir = BV.minimal[node.x].a;
            }
        }
        _last_bb = _make_Intervals( BV.minimal );
       }
       return deleted_object;
	};
		
	// This is my special addition to the world of r-trees
	// every other (simple) method I found produced crap trees
	// this skews insertions to prefering squarer and emptier nodes
	var _jons_ratio = function(intervals, count) {
	  // Area of new enlarged rectangle
		var i, sum = 0, mul = 1;
		for( i = 0; i < _Dimensions; i++ )
		{
			sum +=  intervals[i].b;
			mul *=  intervals[i].b;
		}
		sum /= dimensions;
	  var lgeo = mul / Math.pow(sum, _Dimensions);
		
	  // return the ratio of the perimeter to the area - the closer to 1 we are, 
	  // the more "square" or "cubic" a volume is. conversly, when approaching zero the 
	  // more elongated a rectangle is
	  return(mul * count / lgeo); 
	};
	
	_split_Leaf = function(leaf) {
		var nodes = _linear_split(leaf.n);
		return _make_Node(nodes[0], nodes[1]);
	};
	/* split a set of nodes into two roughly equally-filled nodes
	 * [ an array of two new arrays of nodes ] = linear_split(array of nodes)
	 * @private
	 */
	var _linear_split = function(nodes) {
		var n = _pick_linear(nodes);
		while(nodes.length > 0)	{
			_pick_next(nodes, n[0], n[1]);
		}
		return(n);
	};
	
	/* insert the best source rectangle into the best fitting parent node: a or b
	 * [] = pick_next(array of source nodes, target node array a, target node array b)
	 * @private
	 */
	var _pick_next = function(nodes, a, b) {
	  // Area of new enlarged rectangle
		var area_a = _jons_ratio(a.i, a.n.length+1);
		var area_b = _jons_ratio(b.i, b.n.length+1);
		var high_area_delta;
		var high_area_node;
		var lowest_growth_group;
		
		for(var i = nodes.length-1; i>=0;i--) {
			var l = nodes[i];

			var copy_of_intervals = _make_Intervals(a.i);
			_expand_Intervals(copy_of_intervals, l.i);
			var change_new_area_a = Math.abs(_jons_ratio(copy_of_intervals, a.n.length+2) - area_a);
	
			copy_of_intervals = _make_Intervals(b.i);
			_expand_Intervals(copy_of_intervals, l.i);
			var change_new_area_b = Math.abs(_jons_ratio(copy_of_intervals, b.n.length+2) - area_b);

			if( !high_area_node || !high_area_delta || Math.abs( change_new_area_b - change_new_area_a ) < high_area_delta ) {
				high_area_node = i;
				high_area_delta = Math.abs(change_new_area_b-change_new_area_a);
				lowest_growth_group = change_new_area_b < change_new_area_a ? b : a;
			}
		}
		var temp_node = nodes.splice(high_area_node, 1)[0];
/*		if(a.n.length + nodes.length + 1 <= _Min_Width)	{
			a.n.push(temp_node);
			_expand_intervals(a.i, temp_node.i);
		}	else if(b.n.length + nodes.length + 1 <= _Min_Width) {
			b.nodes.push(temp_node);
			_expand_intervals(b.i, temp_node.i);
		}
		else {*/
			lowest_growth_group.n.push(temp_node);
			_expand_Intervals(lowest_growth_group.i, temp_node.i);
//		}
	};

	/* pick the "best" two starter nodes to use as seeds using the "linear" criteria
	 * [ an array of two new arrays of nodes ] = pick_linear(array of source nodes)
	 * @private
	 */
	var _pick_linear = function(nodes) {
		var lowest_high = new Array(_Dimensions);
		for(i = 0; i < _Dimensions;i++)	lowest_high[i] = nodes.length-1;
		var highest_low = new Array(_Dimensions);
		for(i = 0; i < _Dimensions;i++)	highest_low[i] = 0;
    var t1, t2, l, i, d;
		
		for(i = nodes.length-2; i>=0;i--)	{
			l = nodes[i];
			for(d = 0; d < _Dimensions;d++)	{
				if(l.i[d].a > nodes[highest_low[d]].i[d].a ) {
					highest_low[d] = i;
				}
				else if(l.i[d].a+l.i[d].b < nodes[lowest_high[d]].i[d].a+nodes[lowest_high[d]].i[d].b) {
					lowest_high[d] = i;
				}
			}
		}
		
		d = 0;
		var difference, last_difference = 0;
		for(i = 0; i < _Dimensions;i++)	{
			difference = Math.abs((nodes[lowest_high[i]].i[i].a+nodes[lowest_high[i]].i[i].b) - nodes[highest_low[i]].i[i].a);
			if(difference > last_difference)
			{
				d = i;
				last_difference = difference;
			}
		}		
		
		if(lowest_high[d] > highest_low[d])	{
			t1 = nodes.splice(lowest_high[d], 1)[0];
			t2 = nodes.splice(highest_low[d], 1)[0];
		}	else {
			t2 = nodes.splice(highest_low[d], 1)[0];
			t1 = nodes.splice(lowest_high[d], 1)[0];
		}

		return([{i:_make_Intervals(t1.i), n:[t1]},
			      {i:_make_Intervals(t2.i), n:[t2]} ]);
	};
	
    this.last_bb = function(){
       return _last_bb;
    };
    
	/* non-recursive internal insert function
	 * [] = _insert_subtree(rectangle, object to insert, root to begin insertion at)
	 * @private
	 */
	var _insert_subtree = function(options) {
		if( !("item" in options) ) {
			options.item = {i:options.intervals, o:options.object};
		}
		var item = options.item;
		var root = options.root;
		var comparators = options.comparators;

        if( _E == null ) {
            // Copy Object intervals
            _E = _make_Intervals(item.i)
        } else {
            // Enlarge envelope if necessary
            _expand_Intervals(_E, item.i);
        }

		// Initial insertion is special
		if( _T == null ) {
			_T = item;
			return;
		}

		if( "n" in _T ) {		// If the root of the tree is just collection of leaves...
		    if(_T.n.length+1 < _Max_Leaf_Size)
		    {
              _expand_Intervals(_T.i, item.i);
              _T.n.push(item);
		    }else {
              _T.n.push(item);
    	        _T = _split_Leaf(_T);
    		}
    		return;
    } else if( "o" in _T ){		// If the root of the tree is just a leaf...
    		var new_node = {i:_make_Intervals(_T.i),n:[]};
    		_expand_Intervals(new_node.i, item.i);
    		new_node.n.push(_T);
    		new_node.n.push(item);
    		_T = new_node;
    		return;
    }

		// Otherwise we have to dig
		node = root;

		while(true) { // a return below exits this loop.
            if( _choose_Left(item, node) ){
	            node.il = Math.max( item.i[node.x].a + item.i[node.x].b, node.il );
                if("n" in node.l) {
                    if(node.l.n.length+1 < _Max_Leaf_Size)
                    {
                        _expand_Intervals(node.l.i, item.i);
                        node.l.n.push(item);
                    }else {
                        node.l.n.push(item);
                        node.l = _split_Leaf(node.l);
                    }
   		          //  node.l = _make_Node(item, node.l);
		            return;
		        } else {
                   node = node.l;
                }
            } else {
	            node.ir = Math.min( item.i[node.x].a, node.ir );
                if("n" in node.r) {
                    if(node.r.n.length+1 < _Max_Leaf_Size)
                    {
                        _expand_Intervals(node.r.i, item.i);
                        node.r.n.push(item);
                    }else {
                        node.r.n.push(item);
                        node.r = _split_Leaf(node.r);
                    }
                  //  node.r = _make_Node(item, node.r);
		            return;
		        } else {
                   node = node.r;
                }
            }
        } // end of while
	};

	/* non-recursive internal yield_to function
	 * [ nodes | objects ] = _yield( options )
	 * @private
	 */
	var _yield_to = function(options) {
		var hit_stack = []; // Contains the nodes that overlap
		var intervals = options.intervals;
		var root = options.root;
		var comparators = options.comparators;
        var node = null;
        var yield_leaf = options.yield.leaf;
        var yield_node = options.yield.node;
		if( root != null ){
		    hit_stack.push(root);
		}

		while(hit_stack.length > 0) {
          node = hit_stack.pop(); // Depth-First Descent
        // node = hit_stack.shift(); // Breadth-First Descent

          if("x" in node) { // A node!
            yield_node(node);
            if( comparators.overlap_right(intervals, node) ) {
                hit_stack.push(node.r);
            }
            if( comparators.overlap_left(intervals, node) ) {
                hit_stack.push(node.l);
            }
          } else if("n" in node) { // A collect of leaves!!
    			  if( comparators.overlap_intervals(intervals, node.i) ) {
			  			hit_stack = hit_stack.concat(node.n);
                  }
              } else if("o" in node) { // A leaf!!
            if(comparators.overlap_intervals(intervals, node.i)) {
                yield_leaf(node);
            }
          }  
        }
		return;
	};

	/* non-recursive internal search function 
	 * [ nodes | objects ] = _search_subtree( options )
	 * @private
	 */
	var _search_subtree = function(options) {
		var hit_stack = []; // Contains the nodes that overlap
		var intervals = options.intervals;
		var return_node = options.return_nodes;
		var return_array = options.return_array;
		var root = options.root;
		var comparators = options.comparators;
        var node = null;

		if( root != null ){
		    hit_stack.push(root);
		}
	
		while(hit_stack.length > 0) {
			 node = hit_stack.pop(); // Depth-First Descent
			// node = hit_stack.shift(); // Breadth-First Descent
              if("x" in node) { // A node!
                if( comparators.overlap_right(intervals, node) ) {
        		    hit_stack.push(node.r);
                }
                if( comparators.overlap_left(intervals, node) ) {
        		    hit_stack.push(node.l);
                }
              } else if("n" in node) { // A collect of leaves!!
    			  if( comparators.overlap_intervals(intervals, node.i) ) {
			  			hit_stack = hit_stack.concat(node.n);
                  }
              } else if("o" in node) { // A leaf!!
    			  if( comparators.overlap_intervals(intervals, node.i) ) {
			  		if( !return_node ) {
		  				return_array.push(node.o);
		  			} else {
		  				return_array.push(node);
		  			}
                  }
              } 
        }
		return(return_array);
	};

	/* recursive(?) toJSON function
	 * [ nodes | objects ] = toJSON( )
	 */
	this.toJSON = function() {
        return JSON.stringify(_T);
	};
	/* quick 'n' dirty function for plugins or manually drawing the tree
	 * [ tree ] = ITree.get_tree(): returns the raw tree data. useful for adding
	 * @public
	 * !! DEPRECATED !!
	 */
	this.get_tree = function() {
		return _T;
	};

	/* quick 'n' dirty function for plugins or manually loading the tree
	 * [ tree ] = ITree.set_tree(sub-tree, where to attach): returns the raw tree data. useful for adding
	 * @public
	 * !! DEPRECATED !!
	 */
	this.set_tree = function(new_tree, where) {
		if(!where)
			where = _T;
		return(_attach_data(where, new_tree));
	};

	var _attach_data = function(node, more_tree){
		node = more_tree;
		return(node);
	};

	this.dimensions = function() {
		return _Dimensions;
	}

    this.envelope = function(){
        // Return a copy
        return _make_Intervals(_E);
    }
    
	/* non-recursive yield_to function
	 * ITree.yield_to( options )
	 * @public
	 */
	this.yield_to = function( options ) {
		if(arguments.length < 1) {
			throw "Wrong number of arguments. yield_to() requires an options object."
		}
		if( !("return_nodes" in options) ) {
			options.return_nodes = false; // obj == false for conditionals
		}
		if( !("return_array" in options) ) {
			options.return_array = [];
		}
		if( !("comparators" in options) ) {
			if( !("intervals" in options) ) { // If no comparator object is defined, you must define "intervals".
				throw "Wrong number of options. yield_to() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			}	else {
				options.comparators = {};
			}
		}
		if( !("overlap_intervals" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. yield_to() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_intervals = _overlap_intervals; //Defaults
			}
		}
		if( !("overlap_left" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_left = _overlap_left; //Defaults
			}
		}
		if( !("overlap_right" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_right = _overlap_right; //Defaults
			}
		}

		if( !("yield" in options) ) {
    		options.yield = {};
		}
		if( !("leaf" in options["yield"]) ) {
			options.yield.leaf = function(leaf){}; //Defaults
		}
		if( !("node" in options["yield"]) ) {
			options.yield.node = function(node){}; //Defaults
		}
		options.root = _T; // should not ever be specified by outside

		return( _yield_to( options ) );
	}; /* End of ITree.yield_to() */

	/* non-recursive intersect function
	 * [ nodes | objects ] = ITree.intersect( options )
	 * @public
	 */
	this.intersect = function(options) {
		if(arguments.length < 1) {
			throw "Wrong number of arguments. intersect() requires an options object."
		}
		if( !("return_nodes" in options) ) {
			options.return_nodes = false; // obj == false for conditionals
		}
		if( !("return_array" in options) ) {
			options.return_array = [];
		}
		if( !("ray" in options) ) {
			throw "Wrong number of arguments. intersect() requires a ray."
		}

		options.root = _T; // should not ever be specified by outside

		return( _intersect_subtree( options ) );
	}; /* End of ITree.intersect() */


	/* non-recursive search function 
	 * [ nodes | objects ] = ITree.search( options )
	 * @public
	 */
	this.search = function(options /*intervals, return_node, return_array*/) {
		if(arguments.length < 1) {
			throw "Wrong number of arguments. search() requires an options object."
		}
		if( !("return_nodes" in options) ) {
			options.return_nodes = false; // obj == false for conditionals
		}
		if( !("return_array" in options) ) {
			options.return_array = [];
		}
		if( !("comparators" in options) ) {
			if( !("intervals" in options) ) { // If no comparator object is defined, you must define "intervals".
				throw "Wrong number of options. search() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			}	else {
				options.comparators = {};
			}
		}
		if( !("overlap_intervals" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. search() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_intervals = _overlap_intervals; //Defaults
			}
		}
		if( !("overlap_left" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_left = _overlap_left; //Defaults
			}
		}
		if( !("overlap_right" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_right = _overlap_right; //Defaults
			}
		}

		options.root = _T; // should not ever be specified by outside

		return( _search_subtree( options ) );
	}; /* End of ITree.search() */
		
			
	/* non-recursive insert function
	 * [] = ITree.insert( options )
	 */
	this.insert = function(options/*intervals, obj*/) {
		if(arguments.length < 1) {
			throw "Wrong number of arguments. insert() requires an options object."
		}
		if( !("object" in options) ) {
			throw "Wrong number of options. insert() requires an object to insert.";
		}
		if( !("comparators" in options) ) {
			if( !("intervals" in options) ) { // If no comparator object is defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators = {};
			}
		}
		if( !("overlap_intervals" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_intervals = _overlap_intervals; //Defaults
			}
		}
		if( !("overlap_left" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_left = _overlap_left; //Defaults
			}
		}
		if( !("overlap_right" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_right = _overlap_right; //Defaults
			}
		}
		options.root = _T; // should not ever be specified by outside
		
		return( _insert_subtree( options ) );
	}; /* End of ITree.insert() */

	/* non-recursive function that deletes a specific
	 * [ number ] = ITree.remove( options )
	 */
	this.remove = function(options) {
		if(arguments.length < 1) {
			throw "Wrong number of arguments. remove() requires an options object."
		}
		if( !("object" in options) ) {
			options.object = false; 
		}
		if( !("optimized_remove" in options) ) {
			options.optimized_remove = false; 
		}
		if( !("comparators" in options) ) {
			if( !("intervals" in options) ) { // If no comparator object is defined, you must define "intervals".
				throw "Wrong number of options. remove() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators = {};
			}
		}
		if( !("overlap_intervals" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. remove() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_intervals = _overlap_intervals; //Defaults
			}
		}
		if( !("overlap_left" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_left = _overlap_left; //Defaults
			}
		}
		if( !("overlap_right" in options["comparators"]) ) {
			if( !("intervals" in options) ) { // If no default comparators are defined, you must define "intervals".
				throw "Wrong number of options. insert() requires at least a set of intervals of " + _Dimensions + "-dimensions.";
			} else if( options.intervals.length != _Dimensions ) {
				throw "Wrong number of dimensions in input volume. The tree has a rank of " + _Dimensions + "-dimensions.";
			} else {
				options.comparators.overlap_right = _overlap_right; //Defaults
			}
		}

        var ret_array = [];
		var removed_object;
		if(options.object === false) { // Do area-wide delete
			var number_deleted = 0;
			do {
			    // We have to update "root" because _T could have been changed by a previous _remove_subtree() 
        		options.root = _T; // should not ever be specified by outside
			    removed_object = _remove_subtree( options );
				if( removed_object != false ) {
				    number_deleted++;
				    ret_array.push( removed_object );
				} else {
				    return ret_array;
				}
			}while( true );
		}
		else { // Delete a specific item
       		options.root = _T; // should not ever be specified by outside
            removed_object = _remove_subtree( options );
            if( removed_object != false ) {
                ret_array.push(removed_object);
            }
    	    return ret_array;
		}
	}; /* End of ITree.remove() */

}; /* End of ITree */
