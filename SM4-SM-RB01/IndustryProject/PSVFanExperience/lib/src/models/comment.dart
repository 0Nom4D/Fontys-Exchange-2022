class Comment {
  Comment({
    required this.body,
    required this.username
  });

  final String body;
  final String username;
  bool isLikedByStaff = false;
  bool isLikeByUser = false;
}