'''
Created on Sep 18, 2021

@author: mballance
'''

from vsc.model.bin_expr_type import BinExprType
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.expr_model import ExprModel
from vsc.model.expr_partselect_model import ExprPartselectModel
from vsc.model.field_model import FieldModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.rand_set import RandSet
from vsc.model.rand_state import RandState
from vsc.model.variable_bound_model import VariableBoundModel
import os

class SolveGroupSwizzlerPartsel(object):
    cached = {}
    
    def __init__(self, randstate, solve_info, debug=0):
        self.debug = debug
        self.randstate : RandState = randstate
        self.solve_info = solve_info
    
    def swizzle(self, 
                btor,
                rs : RandSet,
                bound_m : VariableBoundModel):
        if self.debug > 0:
            print("--> swizzle_randvars")

        swizzled_field = False
        # For each random variable, select a partition with it's known 
        # domain and add the corresponding constraint
        field_l = rs.rand_fields()
            
        if self.debug > 0:
            print("  " + str(len(field_l)) + " fields in randset")

        if 'PYVSC_CACHE_RANGE' in os.environ:
            # Use temporary file to dump boolector model
            # TODO Is there a way to redirect stdout from compiled python libraries?
            # TODO Add feature to boolector to get hash or model directly?
            tmp_model_file = '.pyvsc_model'
            btor.Dump(format='btor', outfile=tmp_model_file)
            model_key = open(tmp_model_file).read()
            os.remove(tmp_model_file)

            # Check if we've explored min/max before
            if not model_key in self.cached:
                self.cached[model_key] = {}
                for f in rs.rand_fields():
                    if f in bound_m.keys():
                        f_bound = bound_m[f]
                        if not f_bound.isEmpty():
                            range_l = f_bound.domain.range_l
                            # TODO How to handle multiple ranges?
                            t_range = range_l[0]

                            maxval = int(max(abs(t_range[0]), abs(t_range[1])))
                            d_width = 0
                            while maxval > 0:
                                d_width += 1
                                maxval >>= 1

                            if self.debug: print('before', f, t_range, d_width)
                            t_range, d_width = self.find_max(f, btor, t_range, d_width)
                            t_range, d_width = self.find_min(f, btor, t_range, d_width)
                            f_bound.domain.range_l[0] = t_range
                            if self.debug: print('after', f, t_range, d_width)
                            self.cached[model_key][str(f)] = (t_range, d_width)

                            # TODO Try setting rand_state and randomly solving using new ranges
            else:
                for f in rs.rand_fields():
                    if f in bound_m.keys():
                        f_bound = bound_m[f]
                        if not f_bound.isEmpty():
                            t_range, d_width = self.cached[model_key][str(f)]
                            f_bound.domain.range_l[0] = t_range
                            if self.debug: print('found', f, t_range, d_width)

        if rs.rand_order_l is not None:
            # Perform an ordered randomization
            for ro_l in rs.rand_order_l:
                swizzled_field |= self.swizzle_field_l(ro_l, rs, bound_m, btor)
        else:
            swizzled_field |= self.swizzle_field_l(rs.rand_fields(), rs, bound_m, btor)
                
        if not swizzled_field:
            if self.solve_info is not None:
                self.solve_info.n_sat_calls += 1                    
            btor.Sat()
            
        if self.debug > 0:
            print("<-- swizzle_randvars")    
            
    def swizzle_field_l(self, field_l, rs : RandSet, bound_m, btor):
        if len(field_l) > 0:
            # Make a copy of the field list so we don't
            # destroy the original
            field_l = field_l.copy()
            
            swizzle_node_l = []
            rand_range_l = []
            max_swizzle = 4

            # Select up to `max_swizzle` fields to swizzle            
            for i in range(max_swizzle):
                if len(field_l) > 0:
                    field_idx = self.randstate.randint(0, len(field_l)-1)
                    f = field_l.pop(field_idx)
                    e_l, t_range = self.swizzle_field(f, rs, bound_m, btor)
                    # print(f.name, e_l, t_range)
                    if e_l is not None:
                        for e in e_l:
                            swizzle_node_l.append(e.build(btor))
                        rand_range_l.append((f, t_range))
                else:
                    break

                if 'PYVSC_TRUE_RANGE' in os.environ:
                    # Each entry in the nodelist corresponds to a field
                    while (len(swizzle_node_l) > 0):
                        idx = self.randstate.randint(0, len(swizzle_node_l)-1)
                        n = swizzle_node_l.pop(idx)
                        btor.Assume(n)
                        if self.solve_info is not None:
                            self.solve_info.n_sat_calls += 1
                        if btor.Sat() == btor.SAT:
                            if self.debug > 0:
                                print("  Constraint SAT")
                            btor.Assert(n)
                        else:
                            if self.debug > 0:
                                print("  Constraint UNSAT")

            if not 'PYVSC_TRUE_RANGE' in os.environ:
                rand_range_tries = 0
                if 'PYVSC_RAND_RANGE' in os.environ:
                    rand_range_tries = 4
                    while rand_range_tries > 0:
                        vals = []
                        for f, t_range in rand_range_l:
                            if self.debug > 0:
                                print(f'  {f.name} {t_range}')
                            if t_range[0] == t_range[1]:
                                val = t_range[0]
                            else:
                                val = self.randstate.randint(t_range[0], t_range[1])
                            vals.append((f, val))
                            btor.Assume(ExprBinModel(
                                ExprFieldRefModel(f),
                                BinExprType.Eq,
                                ExprLiteralModel(val, False, 32)).build(btor))
                        if btor.Sat() == btor.SAT:
                            if self.debug > 0:
                                print("  Constraint SAT")
                            for f, val in vals:
                                btor.Assert(ExprBinModel(
                                    ExprFieldRefModel(f),
                                    BinExprType.Eq,
                                    ExprLiteralModel(val, False, 32)).build(btor))
                            break
                        else:
                            if self.debug > 0:
                                print("  Constraint UNSAT")
                            rand_range_tries -= 1

                if rand_range_tries == 0:
                    # Each entry in the nodelist corresponds to a field
                    while (len(swizzle_node_l) > 0):
                        idx = self.randstate.randint(0, len(swizzle_node_l)-1)
                        n = swizzle_node_l.pop(idx)
                        btor.Assume(n)
                        if self.solve_info is not None:
                            self.solve_info.n_sat_calls += 1
                        if btor.Sat() == btor.SAT:
                            if self.debug > 0:
                                print("  Constraint SAT")
                            btor.Assert(n)
                        else:
                            if self.debug > 0:
                                print("  Constraint UNSAT")

            if self.solve_info is not None:
                self.solve_info.n_sat_calls += 1
            if btor.Sat() != btor.SAT:
                raise Exception("failed to add in randomization (2)")                           
            return True
        else:
            return False            

    def swizzle_field(self,
                      f : FieldScalarModel,
                      rs : RandSet,
                      bound_m : VariableBoundModel,
                      btor)->tuple[ExprModel, tuple[int, int]]:
        ret = None
        t_range = (None, None)
        
        if self.debug > 0:
            print("Swizzling field %s" % f.name)
             
        if f in rs.dist_field_m.keys():
            if self.debug > 0:
                print("Note: field %s is in dist map" % f.name)
                for d in rs.dist_field_m[f]:
                    print("  Weight list %s" % d.weight_list)
            if len(rs.dist_field_m[f]) > 1:
                target_d = self.randstate.randint(0, len(rs.dist_field_m[f])-1)
                dist_scope_c = rs.dist_field_m[f][target_d]
            else:
                dist_scope_c = rs.dist_field_m[f][0]
                
            target_range = dist_scope_c.next_target_range(self.randstate)
            target_w = dist_scope_c.dist_c.weights[target_range]
            if target_w.rng_rhs is not None:
                # Dual-bound range
                val_l = target_w.rng_lhs.val()
                val_r = target_w.rng_rhs.val()
                val = self.randstate.randint(val_l, val_r)
                if self.debug > 0:
                    print("Select dist-weight range: %d..%d ; specific value %d" % (
                        int(val_l), int(val_r), int(val)))
                ret = [ExprBinModel(
                    ExprFieldRefModel(f),
                    BinExprType.Eq,
                    ExprLiteralModel(val, f.is_signed, f.width))]
                t_range = (val, val)
            else:
                # Single value
                val = target_w.rng_lhs.val()
                if self.debug > 0:
                    print("Select dist-weight value %d" % (int(val)))
                ret = [ExprBinModel(
                    ExprFieldRefModel(f),
                    BinExprType.Eq,
                    ExprLiteralModel(int(val), f.is_signed, f.width))]
                t_range = (val, val)
        else:
            if f in bound_m.keys():
                f_bound = bound_m[f]
                if not f_bound.isEmpty():
                    ret, t_range = self.create_rand_domain_constraint(f, f_bound, btor)
                    
        return ret, t_range
    
    def create_rand_domain_constraint(self, 
                f : FieldScalarModel, 
                bound_m : VariableBoundModel,
                btor)->tuple[ExprModel, tuple[int, int]]:
        e = []
        range_l = bound_m.domain.range_l
        
        if self.debug:
            print("range_l: %d (%s)" % (len(range_l), str(range_l)))
        if len(range_l) > 1:
            # If we have a multi-part domain, select from one 
            # of the slices
            range_idx = self.randstate.randint(0, len(range_l)-1)
            t_range = range_l[range_idx]
        else:
            # Otherwise, if our domain is a single range, select
            # an appropriate value and slice it into selections
            t_range = range_l[0]
            
        if self.debug > 0:
            print("Domain: %d..%d" % (t_range[0], t_range[1]))
        if t_range[0] == t_range[1]:
            # Single value
            e.append(ExprBinModel(
                        ExprFieldRefModel(f),
                        BinExprType.Eq,
                        ExprLiteralModel(t_range[0], False, 32)))
        else:
            # Determine the max width to use for swizzling. 
            # max value of abs bounds

            maxval = int(max(abs(t_range[0]), abs(t_range[1])))

            d_width = 0
            
            while maxval > 0:
                d_width += 1
                maxval >>= 1
    
            if self.debug > 0:
                print("d_width: %d" % d_width)                

            if 'PYVSC_MINMAX' in os.environ or 'PYVSC_TRUE_RANGE' in os.environ:
                t_range, d_width = self.find_max(f, btor, t_range, d_width)
                t_range, d_width = self.find_min(f, btor, t_range, d_width)

            bit_pattern = self.randstate.randint(t_range[0], t_range[1])
            e = self._build_swizzle_constraints(f, bit_pattern, d_width)

        return e, t_range

    def find_max(self, f, btor, t_range, d_width):
        btor.Assume(ExprBinModel(
            ExprFieldRefModel(f),
            BinExprType.Eq,
            ExprLiteralModel(t_range[1], False, 32)).build(btor))
        if self.solve_info is not None:
            self.solve_info.n_sat_calls += 1
        if btor.Sat() == btor.SAT:
            if self.debug > 0:
                print("  current max: Constraint SAT")
            return t_range, d_width

        skip_size = 6
        skip_d_width = d_width
        for i in range(d_width)[::-skip_size]:
            if i < skip_size:
                break
            b = ExprBinModel(
                    ExprPartselectModel(
                        ExprFieldRefModel(f),
                        ExprLiteralModel(i,   False, 32),
                        ExprLiteralModel(i-skip_size, False, 32)),
                    BinExprType.Ne,
                    ExprLiteralModel(0, False, skip_size)
                    )

            n = b.build(btor)
            btor.Assume(n)
            if self.solve_info is not None:
                self.solve_info.n_sat_calls += 1
            if btor.Sat() == btor.SAT:
                if self.debug > 0:
                    print(f"  max[{i}]x{skip_size}: Constraint SAT")
                skip_d_width = i
                break
            else:
                if self.debug > 0:
                    print(f"  max[{i}x{skip_size}]: Constraint UNSAT")


        new_maxval = 0
        new_dwidth = 0
        max_e = []
        for i in range(skip_d_width)[::-1]:
            b = ExprBinModel(
                    ExprPartselectModel(
                        ExprFieldRefModel(f),
                        ExprLiteralModel(i, False, 32)),
                    BinExprType.Eq,
                    ExprLiteralModel(1, False, 1)
                    )

            n = b.build(btor)
            btor.Assume(n)
            for m in max_e:
                btor.Assume(m)
            if self.solve_info is not None:
                self.solve_info.n_sat_calls += 1
            if btor.Sat() == btor.SAT:
                if self.debug > 0:
                    print(f"  max[{i}]: Constraint SAT")
                new_maxval |= (1 << i)
                max_e.append(n)
                if new_dwidth == 0:
                    new_dwidth = i+1
            else:
                if self.debug > 0:
                    print(f"  max[{i}]: Constraint UNSAT")
        if self.debug > 0:
            print("  new max: %d" % new_maxval)

        t_range = (t_range[0], min(new_maxval, t_range[1]))
        d_width = new_dwidth
        return t_range,d_width

    def find_min(self, f, btor, t_range, d_width):
        btor.Assume(ExprBinModel(
            ExprFieldRefModel(f),
            BinExprType.Eq,
            ExprLiteralModel(t_range[0], False, 32)).build(btor))
        if self.solve_info is not None:
            self.solve_info.n_sat_calls += 1
        if btor.Sat() == btor.SAT:
            if self.debug > 0:
                print("  current min: Constraint SAT")
            return t_range, d_width

        # TODO Try out skipping here like in max

        new_minval = 0
        min_e = []
        for i in range(d_width)[::-1]:
            b = ExprBinModel(
                    ExprPartselectModel(
                        ExprFieldRefModel(f),
                        ExprLiteralModel(i, False, 32)),
                    BinExprType.Eq,
                    ExprLiteralModel(0, False, 1)
                    )

            n = b.build(btor)
            btor.Assume(n)
            for m in min_e:
                btor.Assume(m)
            if self.solve_info is not None:
                self.solve_info.n_sat_calls += 1
            if btor.Sat() == btor.SAT:
                if self.debug > 0:
                    print("  min: Constraint SAT")
                min_e.append(n)
            else:
                new_minval |= (1 << i)
                if self.debug > 0:
                    print("  min: Constraint UNSAT")
        if self.debug > 0:
            print("  new min: %d" % new_minval)

        t_range = (max(new_minval, t_range[0]), t_range[1])
        return t_range, d_width

    def _build_swizzle_constraints(self, f, bit_pattern, d_width):
        e = []
        # TODO This can cause bias issues if dwidth is far larger than the actual maximum width
        max_intervals = 6

        if self.debug > 0:            
            print("bit_pattern: %s" % bin(bit_pattern))
        
        if d_width > max_intervals:
            interval_w = int(d_width/max_intervals)
            
            for i in range(max_intervals):
                low = i*interval_w
                
                if i+1 == max_intervals:
                    high = d_width-1
                    width = d_width-low
                else:
                    high = (i+1)*interval_w-1
                    width = interval_w

                if self.debug > 0:
                    print("%d..%d 0x%08x" % (
                        low, high, ((bit_pattern >> low) & ((1 << width)-1))))
                e.append(ExprBinModel(
                    ExprPartselectModel(
                        ExprFieldRefModel(f),
                        ExprLiteralModel(high, False, 32),
                        ExprLiteralModel(low, False, 32)),
                    BinExprType.Eq,
                    ExprLiteralModel((bit_pattern >> low) & ((1 << width)-1), False, width)
                    ))
        else:
            # Create a per-bit constraint            
            for i in range(d_width):
                e.append(ExprBinModel(
                    ExprPartselectModel(
                        ExprFieldRefModel(f),
                        ExprLiteralModel(i, False, 32)),
                    BinExprType.Eq,
                    ExprLiteralModel((bit_pattern >> i) & 1, False, 1)
                    ))        
        return e

