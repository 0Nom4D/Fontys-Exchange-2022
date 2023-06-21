class ShootingExercise {
  ShootingExercise({
    required this.exerciseTitle,
    required this.imageAsset,
    required this.rating,
    required this.navigateTo,
  });

  String exerciseTitle;
  String imageAsset;
  int rating;
  String navigateTo;

  static List<ShootingExercise> exerciseItems = [
    ShootingExercise(exerciseTitle: "Free Throws", imageAsset: "m_jordan_throw", rating: 1, navigateTo: "/exercises/shooting/free_throws"),
    ShootingExercise(exerciseTitle: "Mikan Drill", imageAsset: "basket_woman", rating: 1, navigateTo: "")
  ];
}