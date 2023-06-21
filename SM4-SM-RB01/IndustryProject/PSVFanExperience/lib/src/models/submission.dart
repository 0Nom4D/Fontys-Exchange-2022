import 'package:psv_fan_experience/src/models/comment.dart';

class Submission {
  Submission({
    required this.picture,
    required this.isFromAsset,
    required this.caption,
    required this.username,
    required this.competition,
    List<Comment>? comments
  }) : comments = comments ?? [];

  final String picture;
  final bool isFromAsset;
  final String caption;
  final String username;
  final String competition;
  int likes = 0;
  bool isLikedByUser = false;
  List<Comment> comments = [];
}
