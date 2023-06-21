class Achievement {
  Achievement({
    required this.title,
    required this.description,
    required this.imageAsset,
    required this.isLocked,
  });

  String title;
  String description;
  String imageAsset;
  bool isLocked;
}