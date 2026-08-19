"""Node and port classes for Hugr graphs."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field, replace
from enum import Enum
from typing import (
    TYPE_CHECKING,
    ClassVar,
    Generic,
    Protocol,
    TypeVar,
    overload,
)

from typing_extensions import Self

if TYPE_CHECKING:
    from collections.abc import Iterator


class Direction(Enum):
    """Enum over port directions, INCOMING and OUTGOING."""

    INCOMING = 0
    OUTGOING = 1


NodeIdx = int
PortOffset = int


@dataclass(frozen=True, eq=True, order=True)
class _Port:
    node: Node
    offset: PortOffset
    direction: ClassVar[Direction]

    def __hash__(self) -> int:
        # Hash the integer identity directly, avoiding nested dataclass hashes.
        return hash((self.node.idx, self.offset))


@dataclass(frozen=True, eq=True, order=True)
class InPort(_Port):
    """Incoming port, defined by the `node` it belongs to and the port `offset`."""

    direction: ClassVar[Direction] = Direction.INCOMING
    __hash__ = _Port.__hash__

    def __repr__(self) -> str:
        return f"InPort({self.node}, {self.offset})"


class Wire(Protocol):
    """Protocol for objects that can provide a dataflow output port."""

    def out_port(self) -> OutPort:
        """OutPort corresponding to this :class:`Wire`."""
        ...  # pragma: no cover


@dataclass(frozen=True, eq=True, order=True)
class OutPort(_Port, Wire):
    """Outgoing port, defined by the `node` it belongs to and the port `offset`."""

    direction: ClassVar[Direction] = Direction.OUTGOING
    __hash__ = _Port.__hash__

    def out_port(self) -> OutPort:
        return self

    def __repr__(self) -> str:
        return f"OutPort({self.node}, {self.offset})"


class ToNode(Wire, Protocol):
    """Protocol by any object that can be treated as a :class:`Node`."""

    def to_node(self) -> Node:
        """Convert to a :class:`Node`."""
        ...  # pragma: no cover

    @overload
    def __getitem__(self, index: PortOffset) -> OutPort: ...
    @overload
    def __getitem__(self, index: slice) -> Iterator[OutPort]: ...
    @overload
    def __getitem__(self, index: tuple[PortOffset, ...]) -> Iterator[OutPort]: ...

    def __getitem__(
        self, index: PortOffset | slice | tuple[PortOffset, ...]
    ) -> OutPort | Iterator[OutPort]:
        return self.to_node()._index(index)

    def out_port(self) -> OutPort:
        return OutPort(self.to_node(), 0)

    def outputs(self) -> Iterator[OutPort]:
        """Returns an iterator over the output ports of this node."""
        return self[:]

    def __iter__(self) -> Iterator[OutPort]:
        return self.outputs()

    def inp(self, offset: PortOffset) -> InPort:
        """Generate an input port for this node.

        Args:
            offset: port offset.

        Returns:
            Incoming port for this node.

        Examples:
            >>> Node(0).inp(1)
            InPort(Node(0), 1)
        """
        return InPort(self.to_node(), offset)

    def out(self, offset: PortOffset) -> OutPort:
        """Generate an output port for this node.

        Args:
            offset: port offset.

        Returns:
            Outgoing port for this node.

        Examples:
            >>> Node(0).out(1)
            OutPort(Node(0), 1)
        """
        return OutPort(self.to_node(), offset)

    def port(self, offset: PortOffset, direction: Direction) -> InPort | OutPort:
        """Generate a port in `direction` for this node with `offset`.

        Examples:
            >>> Node(0).port(1, Direction.INCOMING)
            InPort(Node(0), 1)
            >>> Node(0).port(1, Direction.OUTGOING)
            OutPort(Node(0), 1)
        """
        if direction == Direction.INCOMING:
            return self.inp(offset)
        else:
            return self.out(offset)


@dataclass(eq=True, order=True)
class Node(ToNode):
    """Node in hierarchical :class:`Hugr <hugr.hugr.Hugr>` graph,
    with globally unique index.
    """

    # The ID of the node.
    idx: NodeIdx
    # Number of output ports for this node, or None if the number is not fixed.
    _num_out_ports: int | None = field(
        default=None, compare=False, repr=False, kw_only=True
    )

    def _index(
        self, index: PortOffset | slice | tuple[PortOffset, ...]
    ) -> OutPort | Iterator[OutPort]:
        match index:
            case PortOffset(index):
                index = self._normalize_index(index)
                return self.out(index)
            case slice():
                start = index.start or 0
                stop = index.stop if index.stop is not None else self._num_out_ports
                if stop is None:
                    msg = (
                        f"{self} does not have a fixed number of output ports. "
                        "Iterating over all output ports is not supported."
                    )
                    raise ValueError(msg)

                start = self._normalize_index(start, allow_overflow=True)
                stop = self._normalize_index(stop, allow_overflow=True)
                step = index.step or 1

                return (self[i] for i in range(start, stop, step))
            case tuple(xs):
                return (self[i] for i in xs)

    def _normalize_index(self, index: int, allow_overflow: bool = False) -> int:
        """Given an index passed to `__getitem__`, normalize it to be within the
        range of output ports.

        Args:
            index: index to normalize.
            allow_overflow: whether to allow indices beyond the number of outputs.
                If True, indices over `self._num_out_ports` will be truncated.

        Returns:
            Normalized index.

        Raises:
            IndexError: if the index is out of range.
        """
        msg = f"Index {index} out of range"

        if self._num_out_ports is not None:
            if index >= self._num_out_ports and not allow_overflow:
                raise IndexError(msg)
            if index < -self._num_out_ports:
                raise IndexError(msg)
        else:
            if index < 0:
                raise IndexError(msg)

        if index >= 0 and self._num_out_ports is not None:
            return min(index, self._num_out_ports)
        elif index >= 0:
            return index
        else:
            assert self._num_out_ports is not None
            return self._num_out_ports + index

    def to_node(self) -> Node:
        return self

    def __repr__(self) -> str:
        return f"Node({self.idx})"

    def __hash__(self) -> int:
        return hash(self.idx)


P = TypeVar("P", InPort, OutPort)


@dataclass(frozen=True, eq=True, order=True)
class _SubPort(Generic[P]):
    port: P
    sub_offset: int = 0

    def __hash__(self) -> int:
        """Hash the flattened port and sub-offset identity."""
        return hash((self.port.node.idx, self.port.offset, self.sub_offset))

    def next_sub_offset(self) -> Self:
        return replace(self, sub_offset=self.sub_offset + 1)


_SO = _SubPort[OutPort]
_SI = _SubPort[InPort]


@dataclass(frozen=True, eq=False)
class _NodeLinks:
    """Bidirectional sparse-subport storage for the links in a HUGR.

    Subport offsets are monotonically allocated per port, and are not reused
    after deletion. The global map retains deterministic link insertion order,
    while the endpoint maps make queries and removals proportional to a port's
    degree without scanning through unused sub-offsets.
    """

    #: All links in global insertion order.
    _items: dict[_SO, _SI] = field(init=False, default_factory=dict)
    #: Links indexed by their outgoing parent port and sub-offset.
    #
    # We use the offset `int` instead of `_SI` to avoid unnecessary hashing.
    _fwd: dict[OutPort, dict[int, _SI]] = field(init=False, default_factory=dict)
    #: Links indexed by their incoming parent port and sub-offset.
    #
    # We use the offset `int` instead of `_SI` to avoid unnecessary hashing.
    _bck: dict[InPort, dict[int, _SO]] = field(init=False, default_factory=dict)
    #: Highest sub-offset allocated for each parent port.
    _max_subs: dict[OutPort | InPort, int] = field(
        init=False, default_factory=dict, repr=False
    )

    def __eq__(self, other: object) -> bool:
        """Compare logical links, ignoring their internal allocation history."""
        if not isinstance(other, _NodeLinks):
            return NotImplemented
        links = Counter((src.port, dst.port) for src, dst in self.items())
        other_links = Counter((src.port, dst.port) for src, dst in other.items())
        return links == other_links

    def _unused_sub_offset(self, port: P) -> _SubPort[P]:
        """Allocate the next monotonic sub-offset for ``port``."""
        max_sub = self._max_subs.get(port, -1)
        self._max_subs[port] = max_sub + 1

        return _SubPort(port, sub_offset=max_sub + 1)

    def establish_link(self, src: OutPort, dst: InPort) -> None:
        """Establish a link using fresh subports at both endpoints."""
        src_sub = self._unused_sub_offset(src)
        dst_sub = self._unused_sub_offset(dst)

        self._items[src_sub] = dst_sub
        self._fwd.setdefault(src, {})[src_sub.sub_offset] = dst_sub
        self._bck.setdefault(dst, {})[dst_sub.sub_offset] = src_sub

    def _delete_left(self, src: _SO) -> None:
        """Delete a link identified by its outgoing subport."""
        dst = self._items.pop(src)

        outgoing = self._fwd[src.port]
        del outgoing[src.sub_offset]
        if not outgoing:
            del self._fwd[src.port]

        incoming = self._bck[dst.port]
        del incoming[dst.sub_offset]
        if not incoming:
            del self._bck[dst.port]

    def delete_link(self, src: OutPort, dst: InPort) -> None:
        """Delete the first link between the given parent ports, if present."""
        outgoing = self._fwd.get(src, {})
        incoming = self._bck.get(dst, {})

        if len(outgoing) <= len(incoming):
            src_sub_offset = next(
                (
                    sub_offset
                    for sub_offset, linked in outgoing.items()
                    if linked.port == dst
                ),
                None,
            )
            src_sub = (
                _SubPort(src, src_sub_offset) if src_sub_offset is not None else None
            )
        else:
            src_sub = next(
                (linked for linked in incoming.values() if linked.port == src), None
            )
        if src_sub is not None:
            self._delete_left(src_sub)

    def disconnect_port(self, port: InPort | OutPort) -> None:
        """Delete every link incident to ``port``."""
        match port:
            case OutPort(_):
                outgoing = tuple(
                    _SubPort(port, sub_offset) for sub_offset in self._fwd.get(port, {})
                )
            case InPort(_):
                outgoing = tuple(self._bck.get(port, {}).values())
        for src in outgoing:
            self._delete_left(src)

    @overload
    def linked_ports(self, port: OutPort) -> Iterator[InPort]: ...

    @overload
    def linked_ports(self, port: InPort) -> Iterator[OutPort]: ...

    def linked_ports(self, port: OutPort | InPort):
        """Iterate ports linked to ``port`` without assuming dense sub-offsets."""
        match port:
            case OutPort(_):
                return (sub.port for sub in self._fwd.get(port, {}).values())
            case InPort(_):
                return (sub.port for sub in self._bck.get(port, {}).values())

    def items(self) -> Iterator[tuple[_SO, _SI]]:
        """Iterate all stored links in insertion order."""
        return iter(self._items.items())
