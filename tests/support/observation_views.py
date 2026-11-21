"""Read one public result view while keeping the common envelope assertions."""

from number_compiler.api.json_output import is_string_object_mapping


def view_value(packet: object, kind: str) -> dict[str, object]:
    assert is_string_object_mapping(packet)
    views = packet["views"]
    assert is_string_object_mapping(views)
    view = views[kind]
    assert is_string_object_mapping(view)
    value = view["value"]
    assert is_string_object_mapping(value)
    return {**packet, **value, "status": view["status"]}


def information_only_view(
    response: object, category: str, kind: str
) -> dict[str, object]:
    assert is_string_object_mapping(response) and response["value"] is None
    information = response["info"]
    assert is_string_object_mapping(information)
    return view_value(information[category], kind)
