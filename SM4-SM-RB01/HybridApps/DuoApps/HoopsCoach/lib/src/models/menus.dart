class MenuItem {
  MenuItem({
    required this.menuTitle,
    required this.imageAsset,
    required this.navigationLink,
  });

  String menuTitle;
  String imageAsset;
  String navigationLink;

  static List<MenuItem> menuItems = [
    MenuItem(menuTitle: "SHOOTING", imageAsset: "shooting_button", navigationLink: "/exercises/shooting"),
    MenuItem(menuTitle: "BALL HANDLING", imageAsset: "handling_button", navigationLink: ""),
    MenuItem(menuTitle: "CARDIO", imageAsset: "cardio_button", navigationLink: "")
  ];
}