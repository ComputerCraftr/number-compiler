"""Source-sensitive Collatz cylinder predicates with affine pullback.

The reusable object in this module is a partial function on an admitted finite
source range.  Its branches are exact 2-adic cylinders and its leaves are
accelerated Collatz affine transports.  Temporal composition pulls the second
predicate back through the first transport, so it never constructs or binds a
concrete midpoint occurrence.

The branch language is genuine source information.  This owner hash-conses
equal residual functions, but makes no constant-size or logarithmic cold-work
claim for arbitrary Collatz sources.
"""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.decision import MultiTerminalDecisionArena
from number_compiler.sequences.collatz.hensel_cylinders import (
    MAX_CYLINDER_BITS,
    HenselAffineBlock,
    HenselCylinder,
)
from devtools.experiments.collatz.physical_support import PhysicalSupport, PhysicalSupportArena


from devtools.experiments.collatz.free_cylinder_consumers import (
    BoundCylinderAction, BoundCylinderEndpoint, FreeCylinderResidualID,
    _ConsumerAction, _ConsumerOutput, _CylinderBranch, _FreeCylinderResidual,
    _GuardTrieNode, _bounded_cylinder_nonempty, _branch_key, _coalesce_sibling_guards,
    _constant_target, _consume_guard,
)


class FreeCylinderResidualArena:
    """Canonical finite-precision Collatz residual-function owner.

    ``primitive(q)`` is exact for every positive odd source using at most
    ``q-2`` bits.  Self-composition consumes that safety margin: an ``N`` event
    residual built from the same primitive is admitted only while the original
    source fits its reported ``max_source_bits``.
    """

    def __init__(
        self,
        *,
        max_precision: int = 2048,
        max_actions: int = 4096,
        max_branches: int = 65536,
        max_pair_checks: int = 1000000,
        max_support_nodes: int = 65536,
    ) -> None:
        values = (max_precision, max_actions, max_branches, max_pair_checks)
        if any(type(value) is not int or value < 1 for value in values):
            raise ValueError("cylinder residual limits must be positive integers")
        if max_precision > MAX_CYLINDER_BITS:
            raise BlockContextBudgetExceeded("cylinder residual precision is too large")
        self.max_precision = max_precision
        self.max_actions = max_actions
        self.max_branches = max_branches
        self.max_pair_checks = max_pair_checks
        self.supports = PhysicalSupportArena(max_nodes=max_support_nodes)
        self._owner = object()
        self._nodes: list[_FreeCylinderResidual] = []
        self._keys: dict[tuple[object, ...], FreeCylinderResidualID] = {}
        self._decisions: dict[int, MultiTerminalDecisionArena] = {}
        self._guard_tries: dict[int, tuple[tuple[_GuardTrieNode, ...], int]] = {}
        self._physical_powers: dict[tuple[int, int], FreeCylinderResidualID] = {}
        self._constant_powers: dict[
            tuple[int, tuple[int, ...]], dict[int, _ConsumerAction]
        ] = {}
        self.primitive_constructions = 0
        self.temporal_compositions = 0
        self.branch_pair_checks = 0
        self.cartesian_pair_upper_bound = 0
        self.guard_node_visits = 0
        self.guard_prefix_prunes = 0
        self.pullback_intersections = 0
        self.source_bit_probes = 0
        self.intern_hits = 0
        self.intern_misses = 0
        self.constant_context_nodes = 0
        self.constant_value_bindings = 0
        self.constant_payload_bits = 0
        self.parity_germ_applications = 0
        self.future_endpoint_consumptions = 0
        self.original_source_bit_probes = 0

    def resolve(self, residual: FreeCylinderResidualID) -> _FreeCylinderResidual:
        if (
            type(residual) is not FreeCylinderResidualID
            or residual.owner is not self._owner
            or type(residual.index) is not int
            or not 0 <= residual.index < len(self._nodes)
        ):
            raise ValueError("foreign Collatz cylinder residual identity")
        return self._nodes[residual.index]

    def _decision_arena(self, precision: int) -> MultiTerminalDecisionArena:
        if not 1 <= precision <= self.max_precision:
            raise BlockContextBudgetExceeded("cylinder predicate precision exceeded")
        found = self._decisions.get(precision)
        if found is None:
            found = MultiTerminalDecisionArena((2,) * precision)
            self._decisions[precision] = found
        return found

    @staticmethod
    def _selectors(cylinder: HenselCylinder, precision: int) -> tuple[int, ...]:
        return tuple(
            1 << ((cylinder.residue >> bit) & 1)
            if bit < cylinder.bits
            else 0b11
            for bit in range(precision)
        )

    def _intern(
        self,
        events: int | None,
        physical_ticks: int | None,
        max_source_bits: int,
        branches: tuple[_CylinderBranch, ...],
    ) -> FreeCylinderResidualID:
        if (events is None) == (physical_ticks is None):
            raise ValueError("a residual needs exactly one temporal coordinate")
        if not branches:
            raise ValueError("free cylinder residual has an empty admitted domain")
        bounded: list[_CylinderBranch] = []
        for branch in branches:
            if not _bounded_cylinder_nonempty(branch.domain, max_source_bits):
                continue
            domain = branch.domain
            if domain.bits > max_source_bits:
                # Inside this explicitly bounded source chart, C(q,r) with
                # q>b and r<2**b is the singleton selected by C(b,r).  The
                # affine leaf remains exact; this is not a global 2-adic
                # cylinder identity.
                domain = HenselCylinder(max_source_bits, domain.residue)
            bounded.append(_CylinderBranch(domain, _consume_guard(branch, max_source_bits)))
        canonical = tuple(
            sorted(set(_coalesce_sibling_guards(bounded)), key=_branch_key)
        )
        if not canonical:
            raise ValueError("free cylinder residual has an empty bounded domain")
        if len(canonical) > self.max_branches:
            raise BlockContextBudgetExceeded("cylinder residual branch budget exceeded")
        precision = max(branch.domain.bits for branch in canonical)
        decisions = self._decision_arena(precision)
        root = decisions.build_labeled_boxes(
            (
                branch.action,
                self._selectors(branch.domain, precision),
            )
            for branch in canonical
        )
        key = (events, physical_ticks, max_source_bits, precision, root)
        found = self._keys.get(key)
        if found is not None:
            self.intern_hits += 1
            return found
        if len(self._nodes) >= self.max_actions:
            raise BlockContextBudgetExceeded("cylinder residual action budget exceeded")
        result = FreeCylinderResidualID(self._owner, len(self._nodes))
        self._nodes.append(
            _FreeCylinderResidual(
                events,
                physical_ticks,
                max_source_bits,
                precision,
                root,
                canonical,
            )
        )
        self._keys[key] = result
        self.intern_misses += 1
        return result

    def primitive(self, precision: int) -> FreeCylinderResidualID:
        """Return every exact one-event valuation branch through precision ``q``."""
        if type(precision) is not int or not 3 <= precision <= self.max_precision:
            raise ValueError("primitive cylinder precision must lie in 3..max_precision")
        branches = tuple(
            _CylinderBranch(
                HenselCylinder.from_root(k + 1, 1, 1 - (1 << k)),
                _ConsumerAction(
                    _ConsumerOutput(transport=HenselAffineBlock(1, k, 1)),
                    self.supports.event(k),
                ),
            )
            for k in range(1, precision)
        )
        self.primitive_constructions += 1
        return self._intern(1, None, precision - 2, branches)

    def physical_primitive(self, source_bits: int) -> FreeCylinderResidualID:
        """Return the exact parity-guarded one-physical-tick action."""
        if type(source_bits) is not int or not 1 <= source_bits <= self.max_precision:
            raise ValueError("physical source width lies outside the arena")
        found = self._physical_powers.get((1, source_bits))
        if found is not None:
            return found
        result = self._intern(
            None,
            1,
            source_bits,
            (
                _CylinderBranch(
                    HenselCylinder(1, 0),
                    _ConsumerAction(
                        _ConsumerOutput(transport=HenselAffineBlock(0, 1, 0)),
                        self.supports.even,
                    ),
                ),
                _CylinderBranch(
                    HenselCylinder(1, 1),
                    _ConsumerAction(
                        _ConsumerOutput(transport=HenselAffineBlock(1, 0, 1)),
                        self.supports.odd,
                    ),
                ),
            ),
        )
        self._physical_powers[(1, source_bits)] = result
        self.primitive_constructions += 1
        return result

    @staticmethod
    def _maximum_output_bits(node: _FreeCylinderResidual, source_bits: int) -> int:
        """Exact monotone affine range enclosure over a bounded source chart."""
        if not 1 <= source_bits <= node.max_source_bits:
            raise ValueError("source width lies outside the residual chart")
        limit = 1 << source_bits
        maximum = 0
        for branch in node.branches:
            if branch.action.output.constant_target is not None:
                maximum = max(maximum, branch.action.output.constant_target)
                continue
            transport = branch.action.output.transport
            if transport is None:
                raise AssertionError("consumer branch has no output")
            residue = branch.domain.residue
            modulus = 1 << branch.domain.bits
            candidate = residue + ((limit - 1 - residue) // modulus) * modulus
            if candidate <= 0 or candidate >= limit:
                continue
            numerator = 3**transport.steps * candidate + transport.offset
            if numerator % (1 << transport.divisions):
                raise AssertionError("cylinder branch lost affine integrality")
            maximum = max(maximum, numerator >> transport.divisions)
        if maximum <= 0:
            raise AssertionError("positive source chart has no positive image")
        return maximum.bit_length()

    def _guard_trie(
        self, residual: FreeCylinderResidualID
    ) -> tuple[tuple[_GuardTrieNode, ...], int]:
        """Build the canonical low-bit prefix DAG for one residual's guards."""
        found = self._guard_tries.get(residual.index)
        if found is not None:
            return found
        node = self.resolve(residual)
        children: list[list[int | None]] = [[None, None]]
        terminals: list[_ConsumerAction | None] = [None]
        for branch in node.branches:
            cursor = 0
            for depth in range(branch.domain.bits):
                if terminals[cursor] is not None:
                    raise AssertionError("cylinder guard has an overlapping ancestor")
                bit = (branch.domain.residue >> depth) & 1
                child = children[cursor][bit]
                if child is None:
                    child = len(children)
                    children[cursor][bit] = child
                    children.append([None, None])
                    terminals.append(None)
                cursor = child
            if terminals[cursor] not in (None, branch.action):
                raise AssertionError("overlapping cylinder guards disagree")
            if any(child is not None for child in children[cursor]):
                raise AssertionError("cylinder guard has overlapping descendants")
            terminals[cursor] = branch.action

        raw_to_canonical = [-1] * len(children)
        canonical: list[_GuardTrieNode] = []
        intern: dict[tuple[object, ...], int] = {}
        for raw in range(len(children) - 1, -1, -1):
            zero_raw, one_raw = children[raw]
            zero = None if zero_raw is None else raw_to_canonical[zero_raw]
            one = None if one_raw is None else raw_to_canonical[one_raw]
            key = (terminals[raw], zero, one)
            guard = intern.get(key)
            if guard is None:
                guard = len(canonical)
                canonical.append(_GuardTrieNode(terminals[raw], zero, one))
                intern[key] = guard
            raw_to_canonical[raw] = guard
        result = (tuple(canonical), raw_to_canonical[0])
        self._guard_tries[residual.index] = result
        return result

    @staticmethod
    def _apply_consumer(action: _ConsumerAction, source: int) -> int:
        if action.output.constant_target is not None:
            return action.output.constant_target
        transport = action.output.transport
        if transport is None:
            raise AssertionError("consumer action has no output")
        numerator = 3**transport.steps * source + transport.offset
        denominator = 1 << transport.divisions
        if numerator % denominator:
            raise AssertionError("consumer action is not integral on its guard")
        return int(numerator // denominator)

    def _then_consumers(
        self, before: _ConsumerAction, after: _ConsumerAction
    ) -> _ConsumerAction:
        if after.output.constant_target is not None:
            output = after.output
        elif before.output.constant_target is not None:
            output = _ConsumerOutput(
                constant_target=self._apply_consumer(
                    after, before.output.constant_target
                )
            )
        else:
            first = before.output.transport
            second = after.output.transport
            if first is None or second is None:
                raise AssertionError("affine consumer composition lost a transport")
            output = _ConsumerOutput(transport=first.then(second))
        return _ConsumerAction(
            output,
            self.supports.concat(before.support, after.support),
        )

    def _select_value(
        self, residual: FreeCylinderResidualID, source: int
    ) -> _ConsumerAction:
        node = self.resolve(residual)
        if source <= 0 or source.bit_length() > node.max_source_bits:
            raise BlockContextBudgetExceeded("constant image left the following chart")
        decisions = self._decision_arena(node.predicate_bits)
        decision = node.decision_root
        while True:
            record = decisions._nodes[decision]
            if record[0] == "T":
                if type(record[1]) is not _ConsumerAction:
                    raise AssertionError("constant image has no following consumer")
                return record[1]
            _, level, entries = record
            coordinate = decisions.order[level]
            bit = 1 << ((source >> coordinate) & 1)
            for child, mask in entries:
                if mask & bit:
                    decision = child
                    break
            else:
                raise AssertionError("consumer decision omitted a Boolean branch")

    def _publish_constant_context(
        self,
        key: tuple[int, tuple[int, ...]],
        mapping: dict[int, _ConsumerAction],
    ) -> None:
        if len(self._constant_powers) >= self.max_actions:
            raise BlockContextBudgetExceeded("constant context budget exceeded")
        if len(mapping) > self.max_branches:
            raise BlockContextBudgetExceeded("constant value support budget exceeded")
        payload_bits = sum(
            source.bit_length()
            + (
                action.output.constant_target.bit_length()
                if action.output.constant_target is not None
                else 0
            )
            for source, action in mapping.items()
        )
        if payload_bits > self.max_branches * self.max_precision:
            raise BlockContextBudgetExceeded("constant context payload budget exceeded")
        self._constant_powers[key] = mapping
        self.constant_context_nodes += 1
        self.constant_value_bindings += len(mapping)
        self.constant_payload_bits += payload_bits

    def _constant_power(
        self, physical_ticks: int, sources: tuple[int, ...]
    ) -> dict[int, _ConsumerAction]:
        """Power the parity germ on one normalized finite image grammar."""
        normalized = tuple(sorted(set(sources)))
        if not normalized or any(source <= 0 for source in normalized):
            raise ValueError("constant image grammar requires positive endpoints")
        if max(source.bit_length() for source in normalized) > self.max_precision:
            raise BlockContextBudgetExceeded("constant image precision exceeded")
        target = physical_ticks, normalized
        pending: list[tuple[int, tuple[int, ...], int]] = [
            (physical_ticks, normalized, 0)
        ]
        partials: dict[
            tuple[int, tuple[int, ...]],
            tuple[dict[int, _ConsumerAction], int, tuple[int, ...]],
        ] = {}
        while pending:
            ticks, context, stage = pending.pop()
            key = ticks, context
            if key in self._constant_powers:
                continue
            if ticks == 1:
                mapping: dict[int, _ConsumerAction] = {}
                for source in context:
                    if source & 1:
                        endpoint, events = 3 * source + 1, 1
                    else:
                        endpoint, events = source // 2, 0
                    mapping[source] = _ConsumerAction(
                        _ConsumerOutput(constant_target=endpoint),
                        self.supports.odd if events else self.supports.even,
                    )
                    self.parity_germ_applications += 1
                    self.future_endpoint_consumptions += 1
                self._publish_constant_context(key, mapping)
                continue
            first_ticks = ticks // 2
            after_ticks = ticks - first_ticks
            first_key = first_ticks, context
            if stage == 0:
                pending.append((ticks, context, 1))
                if first_key not in self._constant_powers:
                    pending.append((first_ticks, context, 0))
                continue
            if stage == 1:
                first = self._constant_powers[first_key]
                if any(
                    action.output.constant_target is None for action in first.values()
                ):
                    raise AssertionError("constant power emitted a nonconstant output")
                image = tuple(
                    sorted(
                        {
                            _constant_target(action)
                            for action in first.values()
                        }
                    )
                )
                partials[key] = first, after_ticks, image
                pending.append((ticks, context, 2))
                if (after_ticks, image) not in self._constant_powers:
                    pending.append((after_ticks, image, 0))
                continue
            first, saved_after_ticks, image = partials.pop(key)
            after = self._constant_powers[(saved_after_ticks, image)]
            mapping = {}
            for source, first_action in first.items():
                midpoint = first_action.output.constant_target
                if midpoint is None:
                    raise AssertionError("finite image map lost its constant")
                mapping[source] = self._then_consumers(
                    first_action,
                    after[midpoint],
                )
            self._publish_constant_context(key, mapping)
        return self._constant_powers[target]

    def compose(
        self,
        first: FreeCylinderResidualID,
        after: FreeCylinderResidualID,
        *,
        source_bits: int | None = None,
    ) -> FreeCylinderResidualID:
        """Substitute ``after`` through ``first`` without a midpoint occurrence."""
        before = self.resolve(first)
        following = self.resolve(after)
        if before.accelerated_events is not None:
            if following.accelerated_events is None:
                raise ValueError("cannot mix accelerated and physical residuals")
            max_source_bits = min(
                before.max_source_bits,
                following.max_source_bits - before.accelerated_events,
            )
            events = before.accelerated_events + following.accelerated_events
            physical_ticks = None
        else:
            if before.physical_ticks is None or following.physical_ticks is None:
                raise ValueError("cannot mix accelerated and physical residuals")
            max_source_bits = before.max_source_bits if source_bits is None else source_bits
            if not 1 <= max_source_bits <= before.max_source_bits:
                raise ValueError("physical composition source chart is invalid")
            output_bits = self._maximum_output_bits(before, max_source_bits)
            if output_bits > following.max_source_bits:
                raise BlockContextBudgetExceeded(
                    "following physical residual does not cover the first image"
                )
            events = None
            physical_ticks = before.physical_ticks + following.physical_ticks
        if max_source_bits < 1:
            raise BlockContextBudgetExceeded("composition exhausted source-bit margin")
        live_left = tuple(
            branch
            for branch in before.branches
            if _bounded_cylinder_nonempty(branch.domain, max_source_bits)
        )
        guard_nodes, guard_root = self._guard_trie(after)
        branches: list[_CylinderBranch] = []
        visits = 0
        prunes = 0
        terminal_checks = 0
        intersections = 0
        for left in live_left:
            left_transport = left.action.output.transport
            if left_transport is None:
                target = left.action.output.constant_target
                if target is None:
                    raise AssertionError("constant branch has no endpoint")
                right = self._select_value(after, target)
                branches.append(
                    _CylinderBranch(
                        left.domain,
                        self._then_consumers(left.action, right),
                    )
                )
                visits += 1
                terminal_checks += 1
                intersections += 1
                continue
            stack = [(guard_root, 0, 0, left.domain)]
            while stack:
                guard, depth, residue, domain = stack.pop()
                visits += 1
                if visits > self.max_pair_checks:
                    raise BlockContextBudgetExceeded(
                        "cylinder guard-trie visit budget exceeded"
                    )
                trie_node = guard_nodes[guard]
                if trie_node.terminal is not None:
                    terminal_checks += 1
                    intersections += 1
                    branches.append(
                        _CylinderBranch(
                            domain,
                            self._then_consumers(left.action, trie_node.terminal),
                        )
                    )
                    continue
                for bit, child in ((1, trie_node.one), (0, trie_node.zero)):
                    if child is None:
                        continue
                    child_depth = depth + 1
                    child_residue = residue | (bit << depth)
                    prefix = HenselCylinder(child_depth, child_residue)
                    pulled = prefix.pullback(left_transport)
                    child_domain = left.domain.intersect(pulled)
                    if child_domain is None or not _bounded_cylinder_nonempty(
                        child_domain, max_source_bits
                    ):
                        prunes += 1
                        continue
                    stack.append((child, child_depth, child_residue, child_domain))
        result = self._intern(
            events,
            physical_ticks,
            max_source_bits,
            tuple(branches),
        )
        self.temporal_compositions += 1
        self.cartesian_pair_upper_bound += len(live_left) * len(following.branches)
        self.branch_pair_checks += terminal_checks
        self.guard_node_visits += visits
        self.guard_prefix_prunes += prunes
        self.pullback_intersections += intersections
        return result

    def power_physical(
        self, physical_ticks: int, source_bits: int
    ) -> FreeCylinderResidualID:
        """Build exact ``C^^ticks`` with source-conditioned second-half charts."""
        if type(physical_ticks) is not int or physical_ticks < 1:
            raise ValueError("physical duration must be positive")
        if type(source_bits) is not int or not 1 <= source_bits <= self.max_precision:
            raise ValueError("physical source width lies outside the arena")
        target = (physical_ticks, source_bits)
        pending: list[tuple[int, int, int]] = [(physical_ticks, source_bits, 0)]
        first_halves: dict[tuple[int, int], tuple[FreeCylinderResidualID, int, int]] = {}
        while pending:
            ticks, bits, stage = pending.pop()
            key = (ticks, bits)
            if key in self._physical_powers:
                continue
            if ticks == 1:
                self.physical_primitive(bits)
                continue
            first_ticks = ticks // 2
            after_ticks = ticks - first_ticks
            first_key = (first_ticks, bits)
            if stage == 0:
                pending.append((ticks, bits, 1))
                if first_key not in self._physical_powers:
                    pending.append((first_ticks, bits, 0))
                continue
            if stage == 1:
                first = self._physical_powers[first_key]
                first_node = self.resolve(first)
                if all(
                    branch.action.output.constant_target is not None
                    for branch in first_node.branches
                ):
                    image = tuple(
                        sorted(
                            {
                                _constant_target(branch.action)
                                for branch in first_node.branches
                            }
                        )
                    )
                    after_constants = self._constant_power(after_ticks, image)
                    branches = tuple(
                        _CylinderBranch(
                            branch.domain,
                            self._then_consumers(
                                branch.action,
                                after_constants[
                                    _constant_target(branch.action)
                                ],
                            ),
                        )
                        for branch in first_node.branches
                    )
                    self._physical_powers[key] = self._intern(
                        None,
                        ticks,
                        bits,
                        branches,
                    )
                    continue
                image_bits = self._maximum_output_bits(self.resolve(first), bits)
                first_halves[key] = (first, after_ticks, image_bits)
                pending.append((ticks, bits, 2))
                if (after_ticks, image_bits) not in self._physical_powers:
                    pending.append((after_ticks, image_bits, 0))
                continue
            first, saved_after_ticks, image_bits = first_halves.pop(key)
            after = self._physical_powers[(saved_after_ticks, image_bits)]
            self._physical_powers[key] = self.compose(
                first,
                after,
                source_bits=bits,
            )
        return self._physical_powers[target]

    def select(
        self,
        residual: FreeCylinderResidualID,
        *,
        source_bits: int,
        source_bit: Callable[[int], int],
    ) -> BoundCylinderAction:
        """Select a block from a source prefix without producing its midpoint.

        ``source_bit(i)`` is the lazy source boundary.  The reduced decision DAG
        requests only source coordinates on its selected path; coordinates at
        or above ``source_bits`` are supplied as zero without a callback.  Only
        the final whole-block affine transport is returned.
        """
        node = self.resolve(residual)
        if type(source_bits) is not int or not 1 <= source_bits <= node.max_source_bits:
            raise ValueError("source exceeds the residual's proved bit bound")
        decisions = self._decision_arena(node.predicate_bits)
        cached_bits: dict[int, int] = {}

        def read(bit: int) -> int:
            if bit >= source_bits:
                return 0
            found = cached_bits.get(bit)
            if found is not None:
                return found
            value = source_bit(bit)
            if type(value) is not int or value not in (0, 1):
                raise ValueError("source-bit callback must return zero or one")
            cached_bits[bit] = value
            self.source_bit_probes += 1
            return value

        if read(source_bits - 1) != 1:
            raise ValueError("source width must identify a positive occurrence")
        if node.accelerated_events is not None and read(0) != 1:
            raise ValueError("accelerated source occurrence must be odd")
        decision = node.decision_root
        while True:
            record = decisions._nodes[decision]
            if record[0] == "T":
                transport = record[1]
                break
            _, level, entries = record
            bit = 1 << read(decisions.order[level])
            for child, mask in entries:
                if mask & bit:
                    decision = child
                    break
            else:
                raise AssertionError("cylinder decision omitted a Boolean branch")
        if type(transport) is not _ConsumerAction:
            raise AssertionError("admitted source has no cylinder consumer")
        return BoundCylinderAction(
            transport.output.constant_target,
            transport.output.transport,
            transport.event_weight,
            transport.physical_ticks,
            transport.support,
        )

    def bind(self, residual: FreeCylinderResidualID, source: int) -> BoundCylinderEndpoint:
        """Convenience exact-integer seam used by differential validation."""
        node = self.resolve(residual)
        if type(source) is not int or source <= 0:
            raise ValueError("cylinder residual source must be positive")
        if node.accelerated_events is not None and not source & 1:
            raise ValueError("accelerated cylinder residual source must be odd")
        selected = self.select(
            residual,
            source_bits=source.bit_length(),
            source_bit=lambda bit: (source >> bit) & 1,
        )
        target = selected.apply_exact(source)
        if target <= 0:
            raise AssertionError("cylinder predicate produced a nonpositive endpoint")
        return BoundCylinderEndpoint(
            target,
            selected.accelerated_events,
            selected.physical_ticks,
        )

    def metrics(self, residual: FreeCylinderResidualID) -> dict[str, int]:
        node = self.resolve(residual)
        decisions = self._decision_arena(node.predicate_bits)
        pending = [node.decision_root]
        seen: set[int] = set()
        internal_nodes = 0
        terminals = 0
        output_ids: set[_ConsumerOutput] = set()
        weighted_ids: set[tuple[_ConsumerOutput, int, int]] = set()
        support_ids: set[PhysicalSupport] = set()
        while pending:
            decision = pending.pop()
            if decision in seen:
                continue
            seen.add(decision)
            record = decisions._nodes[decision]
            if record[0] == "T":
                terminals += 1
                if type(record[1]) is _ConsumerAction:
                    weighted_ids.add((record[1].output, record[1].event_weight,
                                      record[1].physical_ticks))
                    support_ids.add(record[1].support)
                    output_ids.add(record[1].output)
                continue
            internal_nodes += 1
            pending.extend(child for child, _mask in record[2])
        return {
            "accelerated_events": (
                node.accelerated_events if node.accelerated_events is not None else -1
            ),
            "physical_ticks": (
                node.physical_ticks if node.physical_ticks is not None else -1
            ),
            "max_source_bits": node.max_source_bits,
            "branches": len(node.branches),
            "predicate_bits": node.predicate_bits,
            "decision_internal_nodes": internal_nodes,
            "decision_terminals": terminals,
            "consumer_output_ids": len(output_ids),
            "weighted_consumer_ids": len(weighted_ids),
            "support_consumer_ids": len(support_ids),
            "support_arena_nodes": self.supports.node_count,
            "support_compositions": self.supports.compositions,
            "support_intern_hits": self.supports.intern_hits,
            "max_transport_divisions": max(
                (
                    branch.action.output.transport.divisions
                    for branch in node.branches
                    if branch.action.output.transport is not None
                ),
                default=0,
            ),
            "max_transport_offset_bits": max(
                (
                    branch.action.output.transport.offset.bit_length()
                    for branch in node.branches
                    if branch.action.output.transport is not None
                ),
                default=0,
            ),
            "max_constant_target_bits": max(
                (
                    branch.action.output.constant_target.bit_length()
                    for branch in node.branches
                    if branch.action.output.constant_target is not None
                ),
                default=0,
            ),
            "arena_actions": len(self._nodes),
            "branch_pair_checks": self.branch_pair_checks,
            "cartesian_pair_upper_bound": self.cartesian_pair_upper_bound,
            "guard_node_visits": self.guard_node_visits,
            "guard_prefix_prunes": self.guard_prefix_prunes,
            "pullback_intersections": self.pullback_intersections,
            "source_bit_probes": self.source_bit_probes,
            "constant_context_nodes": self.constant_context_nodes,
            "constant_value_bindings": self.constant_value_bindings,
            "constant_payload_bits": self.constant_payload_bits,
            "parity_germ_applications": self.parity_germ_applications,
            "future_endpoint_consumptions": self.future_endpoint_consumptions,
            "original_source_bit_probes": self.original_source_bit_probes,
        }


__all__ = [
    "BoundCylinderAction",
    "BoundCylinderEndpoint",
    "FreeCylinderResidualArena",
    "FreeCylinderResidualID",
]
