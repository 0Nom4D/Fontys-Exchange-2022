import 'package:flutter/cupertino.dart';

import 'package:app/src/models/achievements.dart';

class AchievementProvider extends ChangeNotifier {
  List<Achievement> achievements = [
    Achievement(title: "FIRE IN COURT!!!", imageAsset: "basketball_on_fire_color", description: 'Earn this badge by getting a free throw accuracy of +80%', isLocked: false),
    Achievement(title: "True Pro", imageAsset: "medal", description: '', isLocked: false),
    Achievement(title: "NBA Level", imageAsset: "trophy", description: '', isLocked: true),
    Achievement(title: "KOBE", imageAsset: "trophy", description: '', isLocked: true),
    Achievement(title: "Slam Dunk", imageAsset: "trophy", description: '', isLocked: true),
    Achievement(title: "Learned Parker", imageAsset: "trophy", description: '', isLocked: true),
    Achievement(title: "Hot Ones", imageAsset: "trophy", description: '', isLocked: true),
    Achievement(title: "Henry's Handball", imageAsset: "trophy", description: '', isLocked: true),
  ];

  updateAchievementLockStatus(String achievementTitle) {
    Achievement changed = achievements.firstWhere((element) => element.title == achievementTitle);

    changed.isLocked = !changed.isLocked;
    notifyListeners();
  }
}