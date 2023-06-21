import 'package:psv_fan_experience/src/models/statistic.dart';

class User {
  User({
    required this.userProfilePicture,
    required this.username,
    required this.stats,
  });

  final String userProfilePicture;
  final String username;
  final Statistics stats;

  static User placeholderUser = User(
    userProfilePicture: "assets/images/usericon.png",
    username: "Xavinaldo",
    stats: Statistics(
      points: 1956,
      awards: 2,
      submissions: 7
    ),
  );
}